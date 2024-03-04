//! Functional programming with [`Array`]s.
// This is modeled after `generic-array::functional`
// see: <https://docs.rs/generic-array/1.0.0/generic_array/functional/index.html>

use crate::{Array, ArraySize};

impl<T, U> Array<T, U>
where
    U: ArraySize,
{
    /// Combines two `Array` instances and iterates through both of them, initialization a new
    /// `Array` with the result of the zipped mapping function.
    ///
    /// If the mapping function panics, any already initialized elements in the new array will
    /// be dropped, AND any unused elements in the source arrays will also be dropped.
    #[inline(always)]
    pub fn zip<Rhs, F, O>(self, rhs: Array<Rhs, U>, f: F) -> Array<O, U>
    where
        U: ArraySize,
        F: FnMut(T, Rhs) -> O,
    {
        Zipper {
            inner: self.into_iter(),
            rhs: rhs.into_iter(),
            f,
        }
        .collect()
    }
}

struct Zipper<I, R, F> {
    inner: I,
    rhs: R,
    f: F,
}

impl<I, T, R, RT, O, F> Iterator for Zipper<I, R, F>
where
    I: Iterator<Item = T>,
    R: Iterator<Item = RT>,
    F: FnMut(T, RT) -> O,
{
    type Item = O;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        Some((self.f)(self.inner.next()?, self.rhs.next()?))
    }
}
