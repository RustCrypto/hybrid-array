//! Trait definitions.

use crate::{slice_as_chunks, slice_as_chunks_mut, Array, FromFn};
use core::{
    borrow::{Borrow, BorrowMut},
    ops::{Index, IndexMut, Range},
};
use typenum::Unsigned;

/// Trait which associates a [`usize`] size and `ArrayType` with a
/// `typenum`-provided [`Unsigned`] integer.
///
/// # Safety
///
/// `ArrayType` MUST be an array with a number of elements exactly equal to
/// [`Unsigned::USIZE`]. Breaking this requirement will cause undefined behavior.
///
/// NOTE: This trait is effectively sealed and can not be implemented by third-party crates.
/// It is implemented only for a number of types defined in [`typenum::consts`].
pub unsafe trait ArraySize: Unsigned {
    /// Array type which corresponds to this size.
    type ArrayType<T>: AssociatedArraySize<Size = Self>
        + From<Array<T, Self>>
        + FromFn<T>
        + Into<Array<T, Self>>
        + IntoIterator<Item = T>
        + SliceOps<T>;
}

/// Associates an [`ArraySize`] with a given type.
pub trait AssociatedArraySize: Sized {
    /// Size of an array type, expressed as a [`typenum`]-based [`ArraySize`].
    type Size: ArraySize;
}

impl<T, U> AssociatedArraySize for Array<T, U>
where
    U: ArraySize,
{
    type Size = U;
}

/// Array operations which are const generic over a given array size.
pub trait ArrayOps<T, const N: usize>:
    Borrow<[T; N]>
    + BorrowMut<[T; N]>
    + From<[T; N]>
    + FromFn<T>
    + Into<[T; N]>
    + IntoIterator<Item = T>
    + Sized
    + SliceOps<T>
{
    /// Size of an array as a `usize`.
    ///
    /// Not to be confused with [`AssociatedArraySize::Size`], which is [`typenum`]-based.
    const SIZE: usize;

    /// Returns a reference to the inner array.
    fn as_core_array(&self) -> &[T; N];

    /// Returns a mutable reference to the inner array.
    fn as_mut_core_array(&mut self) -> &mut [T; N];

    /// Create array from Rust's core array type.
    fn from_core_array(arr: [T; N]) -> Self;

    /// Create array reference from reference to Rust's core array type.
    fn ref_from_core_array(arr: &[T; N]) -> &Self;

    /// Create mutable array reference from reference to Rust's core array type.
    fn ref_mut_from_core_array(arr: &mut [T; N]) -> &mut Self;

    /// Returns an array of the same size as `self`, with function `f` applied to each element
    /// in order.
    fn map_to_core_array<F, U>(self, f: F) -> [U; N]
    where
        F: FnMut(T) -> U;

    /// Transform slice to slice of core array type
    fn cast_slice_to_core(slice: &[Self]) -> &[[T; N]];

    /// Transform mutable slice to mutable slice of core array type
    fn cast_slice_to_core_mut(slice: &mut [Self]) -> &mut [[T; N]];

    /// Transform slice to slice of core array type
    fn cast_slice_from_core(slice: &[[T; N]]) -> &[Self];

    /// Transform mutable slice to mutable slice of core array type
    fn cast_slice_from_core_mut(slice: &mut [[T; N]]) -> &mut [Self];
}

impl<T, const N: usize> ArrayOps<T, N> for [T; N] {
    const SIZE: usize = N;

    #[inline]
    fn as_core_array(&self) -> &[T; N] {
        self
    }

    #[inline]
    fn as_mut_core_array(&mut self) -> &mut [T; N] {
        self
    }

    #[inline]
    fn from_core_array(arr: [T; N]) -> Self {
        arr
    }

    #[inline]
    fn ref_from_core_array(array_ref: &[T; N]) -> &Self {
        array_ref
    }

    #[inline]
    fn ref_mut_from_core_array(array_ref: &mut [T; N]) -> &mut Self {
        array_ref
    }

    #[inline]
    fn map_to_core_array<F, U>(self, f: F) -> [U; N]
    where
        F: FnMut(T) -> U,
    {
        self.map(f)
    }

    #[inline]
    fn cast_slice_to_core(slice: &[Self]) -> &[[T; N]] {
        slice
    }

    #[inline]
    fn cast_slice_to_core_mut(slice: &mut [Self]) -> &mut [[T; N]] {
        slice
    }

    #[inline]
    fn cast_slice_from_core(slice: &[[T; N]]) -> &[Self] {
        slice
    }

    #[inline]
    fn cast_slice_from_core_mut(slice: &mut [[T; N]]) -> &mut [Self] {
        slice
    }
}

/// Slice operations which don't have access to a const generic array size.
pub trait SliceOps<T>:
    AsRef<[T]>
    + AsMut<[T]>
    + Borrow<[T]>
    + BorrowMut<[T]>
    + Index<usize>
    + Index<Range<usize>>
    + IndexMut<usize>
    + IndexMut<Range<usize>>
{
    /// Splits the shared slice into a slice of `N`-element arrays.
    ///
    /// See [`slice_as_chunks`] for more information.
    #[inline]
    fn as_array_chunks<N: ArraySize>(&self) -> (&[Array<T, N>], &[T]) {
        slice_as_chunks(self.as_ref())
    }

    /// Splits the exclusive slice into a slice of `N`-element arrays.
    ///
    /// See [`slice_as_chunks_mut`] for more information.
    #[inline]
    fn as_array_chunks_mut<N: ArraySize>(&mut self) -> (&mut [Array<T, N>], &mut [T]) {
        slice_as_chunks_mut(self.as_mut())
    }
}

impl<T> SliceOps<T> for [T] {}
impl<T, const N: usize> SliceOps<T> for [T; N] {}
impl<T, U: ArraySize> SliceOps<T> for Array<T, U> {}
