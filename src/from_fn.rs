//! Support for constructing arrays using a provided generator function.

use crate::{Array, ArraySize};
use core::{
    mem::{self, MaybeUninit},
    ptr,
};

/// Construct an array type from the given generator function.
pub trait FromFn<T>: Sized {
    /// Create array using the given generator function for each element.
    fn from_fn<F>(cb: F) -> Self
    where
        F: FnMut(usize) -> T;

    /// Create an array using the given generator function for each element, returning any errors
    /// which are encountered in the given generator.
    fn try_from_fn<E, F>(cb: F) -> Result<Self, E>
    where
        F: FnMut(usize) -> Result<T, E>;
}

impl<T, U> FromFn<T> for Array<T, U>
where
    U: ArraySize,
{
    #[inline]
    fn from_fn<F>(cb: F) -> Self
    where
        F: FnMut(usize) -> T,
    {
        Array::from_fn(cb)
    }

    #[inline]
    fn try_from_fn<E, F>(cb: F) -> Result<Self, E>
    where
        F: FnMut(usize) -> Result<T, E>,
    {
        Array::try_from_fn(cb)
    }
}

impl<T, const N: usize> FromFn<T> for [T; N] {
    #[inline]
    fn from_fn<F>(cb: F) -> Self
    where
        F: FnMut(usize) -> T,
    {
        core::array::from_fn(cb)
    }

    // TODO(tarcieri): use `array::try_from_fn` when stable
    fn try_from_fn<E, F>(cb: F) -> Result<Self, E>
    where
        F: FnMut(usize) -> Result<T, E>,
    {
        // SAFETY: an array of `MaybeUninit`s is always valid.
        let mut array: [MaybeUninit<T>; N] = unsafe { MaybeUninit::uninit().assume_init() };
        try_from_fn_erased(&mut array, cb)?;

        // TODO(tarcieri): use `MaybeUninit::array_assume_init` when stable
        // SAFETY: if we got here, every element of the array was initialized
        Ok(unsafe { ptr::read(array.as_ptr().cast()) })
    }
}

/// Fills a `MaybeUninit` slice using the given fallible generator function.
///
/// Using a slice avoids monomorphizing for each array size.
#[inline]
fn try_from_fn_erased<T, E, F>(buffer: &mut [MaybeUninit<T>], mut cb: F) -> Result<(), E>
where
    F: FnMut(usize) -> Result<T, E>,
{
    let mut guard = Guard {
        array_mut: buffer,
        initialized: 0,
    };

    while guard.initialized < guard.array_mut.len() {
        let item = cb(guard.initialized)?;

        // SAFETY: the loop's condition ensures we won't push too many items
        unsafe { guard.push_unchecked(item) };
    }

    mem::forget(guard);
    Ok(())
}

/// Drop guard which tracks the total number of initialized items, and handles dropping them in
/// the event a panic occurs.
///
/// Use `mem::forget` when the array has been fully constructed.
struct Guard<'a, T> {
    /// Array being constructed.
    array_mut: &'a mut [MaybeUninit<T>],

    /// Number of items in the array which have been initialized.
    initialized: usize,
}

impl<T> Guard<'_, T> {
    /// Push an item onto the guard, writing to its `MaybeUninit` slot and incrementing the
    /// counter of the number of initialized items.
    ///
    /// # Safety
    ///
    /// This can only be called n-times for as many elements are in the slice.
    #[inline]
    pub unsafe fn push_unchecked(&mut self, item: T) {
        // SAFETY: the `initialized` counter tracks the number of initialized items, so as long as
        // this is called the correct number of times for the array size writes will always be
        // in-bounds and to an uninitialized slot in the array.
        unsafe {
            self.array_mut
                .get_unchecked_mut(self.initialized)
                .write(item);
            self.initialized = self.initialized.saturating_add(1);
        }
    }
}

impl<T> Drop for Guard<'_, T> {
    fn drop(&mut self) {
        debug_assert!(self.initialized <= self.array_mut.len());

        // SAFETY: the slice will only contain initialized items
        unsafe {
            let p: *mut T = self.array_mut.as_mut_ptr().cast();

            for i in 0..self.initialized {
                ptr::drop_in_place(p.add(i));
            }
        }
    }
}
