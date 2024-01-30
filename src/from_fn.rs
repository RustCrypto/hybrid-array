//! Support for constructing arrays using a provided generator function.

use crate::{Array, ArraySize};
use core::{
    convert::Infallible,
    mem::{self, MaybeUninit},
    ptr,
};

impl<T, U> Array<T, U>
where
    U: ArraySize,
{
    /// Create array where each array element `T` is returned by the `f` call.
    #[inline]
    pub fn from_fn<F>(mut f: F) -> Self
    where
        F: FnMut(usize) -> T,
    {
        Self::try_from_fn::<Infallible, _>(|n| Ok(f(n))).expect("should never fail")
    }

    /// Create array fallibly where each array element `T` is returned by the `f` call, or return
    /// an error if any are encountered.
    ///
    /// # Errors
    ///
    /// Propagates the `E` type returned from the provided `F` in the event of error.
    pub fn try_from_fn<E, F>(f: F) -> Result<Self, E>
    where
        F: FnMut(usize) -> Result<T, E>,
    {
        // SAFETY: `Array` is a `repr(transparent)` newtype for `[MaybeUninit<T>; N]`, i.e. an
        // array of uninitialized memory mediated via the `MaybeUninit` interface, which is
        // always valid.
        #[allow(clippy::uninit_assumed_init)]
        let mut array: Array<MaybeUninit<T>, U> = unsafe { MaybeUninit::uninit().assume_init() };
        try_from_fn_erased(array.0.as_mut(), f)?;

        // TODO(tarcieri): use `MaybeUninit::array_assume_init` when stable
        // SAFETY: if we got here, every element of the array was initialized
        Ok(unsafe { ptr::read(array.as_ptr().cast()) })
    }
}

/// Fills a `MaybeUninit` slice using the given fallible generator function.
///
/// Using a slice avoids monomorphizing for each array size.
#[inline]
fn try_from_fn_erased<T, E, F>(buffer: &mut [MaybeUninit<T>], mut f: F) -> Result<(), E>
where
    F: FnMut(usize) -> Result<T, E>,
{
    let mut guard = Guard {
        array_mut: buffer,
        initialized: 0,
    };

    while guard.initialized < guard.array_mut.len() {
        let item = f(guard.initialized)?;

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

        // SAFETY: the loop only iterates over initialized items
        unsafe {
            let p: *mut T = self.array_mut.as_mut_ptr().cast();

            for i in 0..self.initialized {
                ptr::drop_in_place(p.add(i));
            }
        }
    }
}
