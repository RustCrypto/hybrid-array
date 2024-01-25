#![no_std]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![doc = include_str!("../README.md")]
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/RustCrypto/meta/master/logo.svg",
    html_favicon_url = "https://raw.githubusercontent.com/RustCrypto/meta/master/logo.svg"
)]
#![warn(
    clippy::cast_lossless,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_precision_loss,
    clippy::cast_sign_loss,
    clippy::checked_conversions,
    clippy::implicit_saturating_sub,
    clippy::arithmetic_side_effects,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used,
    missing_docs,
    rust_2018_idioms,
    unused_lifetimes,
    unused_qualifications
)]

#[cfg(feature = "std")]
extern crate std;

mod from_fn;
mod iter;
mod sizes;
mod traits;

pub use crate::{from_fn::FromFn, iter::TryFromIteratorError, traits::*};
pub use typenum;
pub use typenum::consts;

use core::{
    array::TryFromSliceError,
    borrow::{Borrow, BorrowMut},
    cmp::Ordering,
    fmt::{self, Debug},
    hash::{Hash, Hasher},
    mem::{ManuallyDrop, MaybeUninit},
    ops::{Add, Deref, DerefMut, Index, IndexMut, Sub},
    ptr,
    slice::{self, Iter, IterMut},
};
use typenum::{Diff, Sum};

#[cfg(feature = "zeroize")]
use zeroize::{Zeroize, ZeroizeOnDrop};

/// Type alias for [`Array`] which is const generic around a size `N`, ala `[T; N]`.
pub type ArrayN<T, const N: usize> = Array<T, <[T; N] as AssociatedArraySize>::Size>;

/// Hybrid typenum-based and const generic array type.
///
/// Provides the flexibility of typenum-based expressions while also
/// allowing interoperability and a transition path to const generics.
#[repr(transparent)]
pub struct Array<T, U: ArraySize>(pub U::ArrayType<T>);

type SplitResult<T, U, N> = (Array<T, N>, Array<T, Diff<U, N>>);
type SplitRefResult<'a, T, U, N> = (&'a Array<T, N>, &'a Array<T, Diff<U, N>>);
type SplitRefMutResult<'a, T, U, N> = (&'a mut Array<T, N>, &'a mut Array<T, Diff<U, N>>);

impl<T, U> Array<T, U>
where
    U: ArraySize,
{
    /// Create array where each array element `T` is returned by the `cb` call.
    pub fn from_fn<F>(cb: F) -> Self
    where
        F: FnMut(usize) -> T,
    {
        Self(FromFn::from_fn(cb))
    }

    /// Create array fallibly where each array element `T` is returned by the `cb` call, or return
    /// an error if any are encountered.
    pub fn try_from_fn<E, F>(cb: F) -> Result<Self, E>
    where
        F: FnMut(usize) -> Result<T, E>,
    {
        FromFn::try_from_fn(cb).map(Self)
    }

    /// Returns an iterator over the array.
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        self.as_ref().iter()
    }

    /// Returns an iterator that allows modifying each value.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        self.as_mut().iter_mut()
    }

    /// Returns a slice containing the entire array. Equivalent to `&s[..]`.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self.0.as_ref()
    }

    /// Returns a mutable slice containing the entire array. Equivalent to `&mut s[..]`.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.0.as_mut()
    }

    /// Convert the given slice into a reference to a hybrid array.
    ///
    /// # Panics
    ///
    /// Panics if the slice's length doesn't match the array type.
    // TODO(tarcieri): deprecate this before the v0.2 release
    // #[deprecated(since = "0.2.0", note = "use TryFrom instead")]
    #[inline]
    pub fn from_slice(slice: &[T]) -> &Self {
        slice.try_into().expect("slice length mismatch")
    }

    /// Convert the given mutable slice to a mutable reference to a hybrid array.
    ///
    /// # Panics
    ///
    /// Panics if the slice's length doesn't match the array type.
    // TODO(tarcieri): deprecate this before the v0.2 release
    // #[deprecated(since = "0.2.0", note = "use TryFrom instead")]
    #[inline]
    pub fn from_mut_slice(slice: &mut [T]) -> &mut Self {
        slice.try_into().expect("slice length mismatch")
    }

    /// Clone the contents of the slice as a new hybrid array.
    ///
    /// # Panics
    ///
    /// Panics if the slice's length doesn't match the array type.
    // TODO(tarcieri): deprecate this before the v0.2 release
    // #[deprecated(since = "0.2.0", note = "use TryFrom instead")]
    #[inline]
    pub fn clone_from_slice(slice: &[T]) -> Self
    where
        Self: Clone,
    {
        slice.try_into().expect("slice length mismatch")
    }

    /// Concatenates `self` with `other`.
    #[inline]
    pub fn concat<N>(self, other: Array<T, N>) -> Array<T, Sum<U, N>>
    where
        N: ArraySize,
        U: Add<N>,
        Sum<U, N>: ArraySize,
    {
        Array::from_iter(self.into_iter().chain(other.into_iter()))
    }

    /// Splits `self` at index `N` in two arrays.
    ///
    /// New arrays hold the original memory from `self`.
    #[inline]
    pub fn split<N>(self) -> SplitResult<T, U, N>
    where
        U: Sub<N>,
        N: ArraySize,
        Diff<U, N>: ArraySize,
    {
        unsafe {
            let array = ManuallyDrop::new(self);
            let head = ptr::read(array.as_ptr().cast());
            let tail = ptr::read(array.as_ptr().add(N::USIZE).cast());
            (head, tail)
        }
    }

    /// Splits `&self` at index `N` in two array references.
    #[inline]
    pub fn split_ref<N>(&self) -> SplitRefResult<'_, T, U, N>
    where
        U: Sub<N>,
        N: ArraySize,
        Diff<U, N>: ArraySize,
    {
        unsafe {
            let array_ptr = self.as_ptr();
            let head = &*array_ptr.cast();
            let tail = &*array_ptr.add(N::USIZE).cast();
            (head, tail)
        }
    }

    /// Splits `&mut self` at index `N` in two mutable array references.
    #[inline]
    pub fn split_ref_mut<N>(&mut self) -> SplitRefMutResult<'_, T, U, N>
    where
        U: Sub<N>,
        N: ArraySize,
        Diff<U, N>: ArraySize,
    {
        unsafe {
            let array_ptr = self.as_mut_ptr();
            let head = &mut *array_ptr.cast();
            let tail = &mut *array_ptr.add(N::USIZE).cast();
            (head, tail)
        }
    }
}

impl<T, U, const N: usize> Array<MaybeUninit<T>, U>
where
    U: ArraySize<ArrayType<MaybeUninit<T>> = [MaybeUninit<T>; N]>,
{
    /// Create an uninitialized array of [`MaybeUninit`]s for the given type.
    pub const fn uninit() -> Self {
        // SAFETY: `Self` is a `repr(transparent)` newtype for `[MaybeUninit<T>; N]`. It is safe
        // to assume `[MaybeUninit<T>; N]` is "initialized" because there is no initialization state
        // for a `MaybeUninit`: it's a type for representing potentially uninitialized memory (and
        // in this case it's uninitialized).
        //
        // This is identical to how `core` implements `MaybeUninit::uninit_array`:
        // <https://github.com/rust-lang/rust/blob/917f654/library/core/src/mem/maybe_uninit.rs#L350-L352>
        // TODO(tarcieri): use `MaybeUninit::uninit_array` when stable
        Self(unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() })
    }

    /// Extract the values from an array of `MaybeUninit` containers.
    ///
    /// # Safety
    ///
    /// It is up to the caller to guarantee that all elements of the array are in an initialized
    /// state.
    pub unsafe fn assume_init(self) -> Array<T, U> {
        // TODO(tarcieri): use `MaybeUninit::array_assume_init` when stable
        Array(ptr::read(self.0.as_ptr().cast()))
    }
}

impl<T, U> AsRef<[T]> for Array<T, U>
where
    U: ArraySize,
{
    #[inline]
    fn as_ref(&self) -> &[T] {
        self.0.as_ref()
    }
}

impl<T, U, const N: usize> AsRef<[T; N]> for Array<T, U>
where
    Self: ArrayOps<T, N>,
    U: ArraySize,
{
    #[inline]
    fn as_ref(&self) -> &[T; N] {
        self.as_core_array()
    }
}

impl<T, U, const N: usize> AsRef<Array<T, U>> for [T; N]
where
    Array<T, U>: ArrayOps<T, N>,
    U: ArraySize,
{
    #[inline]
    fn as_ref(&self) -> &Array<T, U> {
        Array::ref_from_core_array(self)
    }
}

impl<T, U> AsMut<[T]> for Array<T, U>
where
    U: ArraySize,
{
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self.0.as_mut()
    }
}

impl<T, U, const N: usize> AsMut<[T; N]> for Array<T, U>
where
    Self: ArrayOps<T, N>,
    U: ArraySize,
{
    #[inline]
    fn as_mut(&mut self) -> &mut [T; N] {
        self.as_mut_core_array()
    }
}

impl<T, U, const N: usize> AsMut<Array<T, U>> for [T; N]
where
    Array<T, U>: ArrayOps<T, N>,
    U: ArraySize,
{
    #[inline]
    fn as_mut(&mut self) -> &mut Array<T, U> {
        Array::ref_mut_from_core_array(self)
    }
}

impl<T, U> Borrow<[T]> for Array<T, U>
where
    U: ArraySize,
{
    #[inline]
    fn borrow(&self) -> &[T] {
        self.0.as_ref()
    }
}

impl<T, U, const N: usize> Borrow<[T; N]> for Array<T, U>
where
    Self: ArrayOps<T, N>,
    U: ArraySize,
{
    #[inline]
    fn borrow(&self) -> &[T; N] {
        self.as_core_array()
    }
}

impl<T, U> BorrowMut<[T]> for Array<T, U>
where
    U: ArraySize,
{
    #[inline]
    fn borrow_mut(&mut self) -> &mut [T] {
        self.0.as_mut()
    }
}

impl<T, U, const N: usize> BorrowMut<[T; N]> for Array<T, U>
where
    Self: ArrayOps<T, N>,
    U: ArraySize,
{
    #[inline]
    fn borrow_mut(&mut self) -> &mut [T; N] {
        self.as_mut_core_array()
    }
}

impl<T, U> Clone for Array<T, U>
where
    T: Clone,
    U: ArraySize,
{
    #[inline]
    fn clone(&self) -> Self {
        Self::from_fn(|n| self.0.as_ref()[n].clone())
    }
}

impl<T, U> Copy for Array<T, U>
where
    T: Copy,
    U: ArraySize,
    U::ArrayType<T>: Copy,
{
}

impl<T, U> Debug for Array<T, U>
where
    T: Debug,
    U: ArraySize,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Array").field(&self.0.as_ref()).finish()
    }
}

impl<T, U> Default for Array<T, U>
where
    T: Default,
    U: ArraySize,
{
    #[inline]
    fn default() -> Self {
        Self::from_fn(|_| Default::default())
    }
}

impl<T, U> Deref for Array<T, U>
where
    U: ArraySize,
{
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        self.0.as_ref()
    }
}

impl<T, U> DerefMut for Array<T, U>
where
    U: ArraySize,
{
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        self.0.as_mut()
    }
}

impl<T, U> Eq for Array<T, U>
where
    T: Eq,
    U: ArraySize,
{
}

impl<T, U, const N: usize> From<[T; N]> for Array<T, U>
where
    U: ArraySize<ArrayType<T> = [T; N]>,
{
    #[inline]
    fn from(arr: [T; N]) -> Array<T, U> {
        Array(arr)
    }
}

impl<T, U, const N: usize> From<Array<T, U>> for [T; N]
where
    U: ArraySize<ArrayType<T> = [T; N]>,
{
    #[inline]
    fn from(arr: Array<T, U>) -> [T; N] {
        arr.0
    }
}

impl<'a, T, U, const N: usize> From<&'a [T; N]> for &'a Array<T, U>
where
    Array<T, U>: ArrayOps<T, N>,
    U: ArraySize,
{
    #[inline]
    fn from(array_ref: &'a [T; N]) -> &'a Array<T, U> {
        <Array<T, U>>::ref_from_core_array(array_ref)
    }
}

impl<'a, T, U, const N: usize> From<&'a Array<T, U>> for &'a [T; N]
where
    Array<T, U>: ArrayOps<T, N>,
    U: ArraySize,
{
    #[inline]
    fn from(array_ref: &'a Array<T, U>) -> &'a [T; N] {
        array_ref.as_core_array()
    }
}

impl<'a, T, U, const N: usize> From<&'a mut [T; N]> for &'a mut Array<T, U>
where
    Array<T, U>: ArrayOps<T, N>,
    U: ArraySize,
{
    #[inline]
    fn from(array_ref: &'a mut [T; N]) -> &'a mut Array<T, U> {
        <Array<T, U>>::ref_mut_from_core_array(array_ref)
    }
}

impl<'a, T, U, const N: usize> From<&'a mut Array<T, U>> for &'a mut [T; N]
where
    Array<T, U>: ArrayOps<T, N>,
    U: ArraySize,
{
    #[inline]
    fn from(array_ref: &'a mut Array<T, U>) -> &'a mut [T; N] {
        array_ref.as_mut_core_array()
    }
}

impl<T, U> Hash for Array<T, U>
where
    T: Hash,
    U: ArraySize,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.as_ref().hash(state);
    }
}

impl<T, I, U> Index<I> for Array<T, U>
where
    [T]: Index<I>,
    U: ArraySize,
{
    type Output = <[T] as Index<I>>::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        Index::index(self.as_slice(), index)
    }
}

impl<T, I, U> IndexMut<I> for Array<T, U>
where
    [T]: IndexMut<I>,
    U: ArraySize,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        IndexMut::index_mut(self.as_mut_slice(), index)
    }
}

impl<T, U> PartialEq for Array<T, U>
where
    T: PartialEq,
    U: ArraySize,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ref().eq(other.0.as_ref())
    }
}

impl<T, U, const N: usize> PartialEq<[T; N]> for Array<T, U>
where
    T: PartialEq,
    U: ArraySize<ArrayType<T> = [T; N]>,
{
    #[inline]
    fn eq(&self, other: &[T; N]) -> bool {
        self.0.eq(other)
    }
}

impl<T, U, const N: usize> PartialEq<Array<T, U>> for [T; N]
where
    T: PartialEq,
    U: ArraySize<ArrayType<T> = [T; N]>,
{
    #[inline]
    fn eq(&self, other: &Array<T, U>) -> bool {
        self.eq(&other.0)
    }
}

impl<T, U> PartialOrd for Array<T, U>
where
    T: PartialOrd,
    U: ArraySize,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.as_ref().partial_cmp(other.0.as_ref())
    }
}

impl<T, U> Ord for Array<T, U>
where
    T: Ord,
    U: ArraySize,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.as_ref().cmp(other.0.as_ref())
    }
}

/// SAFETY: `Array` is a `repr(transparent)` newtype for `[T; N]`, so as long as `T: Send` it should
/// also be `Send`.
unsafe impl<T, U: ArraySize> Send for Array<T, U> where T: Send {}

/// SAFETY: `Array` is a `repr(transparent)` newtype for `[T; N]`, so as long as `T: Sync` it should
/// also be `Sync`.
unsafe impl<T, U: ArraySize> Sync for Array<T, U> where T: Sync {}

impl<'a, T, U> TryFrom<&'a [T]> for Array<T, U>
where
    Self: Clone,
    U: ArraySize,
{
    type Error = TryFromSliceError;

    #[inline]
    fn try_from(slice: &'a [T]) -> Result<Array<T, U>, TryFromSliceError> {
        <&'a Self>::try_from(slice).map(Clone::clone)
    }
}

impl<'a, T, U> TryFrom<&'a [T]> for &'a Array<T, U>
where
    U: ArraySize,
{
    type Error = TryFromSliceError;

    #[inline]
    fn try_from(slice: &'a [T]) -> Result<Self, TryFromSliceError> {
        check_slice_length::<T, U>(slice)?;

        // SAFETY: `Array<T, U>` is a `repr(transparent)` newtype for a core
        // array with length checked above.
        Ok(unsafe { &*slice.as_ptr().cast() })
    }
}

impl<'a, T, U> TryFrom<&'a mut [T]> for &'a mut Array<T, U>
where
    U: ArraySize,
{
    type Error = TryFromSliceError;

    #[inline]
    fn try_from(slice: &'a mut [T]) -> Result<Self, TryFromSliceError> {
        check_slice_length::<T, U>(slice)?;

        // SAFETY: `Array<T, U>` is a `repr(transparent)` newtype for a core
        // array with length checked above.
        Ok(unsafe { &mut *slice.as_mut_ptr().cast() })
    }
}

#[cfg(feature = "zeroize")]
impl<T, U> Zeroize for Array<T, U>
where
    T: Zeroize,
    U: ArraySize,
{
    #[inline]
    fn zeroize(&mut self) {
        self.0.as_mut().iter_mut().zeroize()
    }
}

#[cfg(feature = "zeroize")]
impl<T, U> ZeroizeOnDrop for Array<T, U>
where
    T: ZeroizeOnDrop,
    U: ArraySize,
{
}

/// Generate a [`TryFromSliceError`] if the slice doesn't match the given length.
#[cfg_attr(debug_assertions, allow(clippy::panic_in_result_fn))]
fn check_slice_length<T, U: ArraySize>(slice: &[T]) -> Result<(), TryFromSliceError> {
    debug_assert_eq!(Array::<(), U>::default().len(), U::USIZE);

    if slice.len() != U::USIZE {
        // Hack: `TryFromSliceError` lacks a public constructor
        <&[T; 1]>::try_from([].as_slice())?;

        #[cfg(debug_assertions)]
        unreachable!();
    }

    Ok(())
}

/// Splits the shared slice into a slice of `N`-element arrays, starting at the beginning
/// of the slice, and a remainder slice with length strictly less than `N`.
///
/// # Panics
/// Panics if `N` is 0.
#[allow(clippy::arithmetic_side_effects)]
#[inline]
pub fn slice_as_chunks<T, N: ArraySize>(buf: &[T]) -> (&[Array<T, N>], &[T]) {
    assert_ne!(N::USIZE, 0, "chunk size must be non-zero");
    // Arithmetic safety: we have checked that `N::USIZE` is not zero, thus
    // division always returns correct result. `tail_pos` can not be bigger than `buf.len()`,
    // thus overflow on multiplication and underflow on substraction are impossible.
    let chunks_len = buf.len() / N::USIZE;
    let tail_pos = N::USIZE * chunks_len;
    let tail_len = buf.len() - tail_pos;
    unsafe {
        let ptr = buf.as_ptr();
        let chunks = slice::from_raw_parts(ptr.cast(), chunks_len);
        let tail = slice::from_raw_parts(ptr.add(tail_pos), tail_len);
        (chunks, tail)
    }
}

/// Splits the exclusive slice into a slice of `N`-element arrays, starting at the beginning
/// of the slice, and a remainder slice with length strictly less than `N`.
///
/// # Panics
/// Panics if `N` is 0.
#[allow(clippy::arithmetic_side_effects)]
#[inline]
pub fn slice_as_chunks_mut<T, N: ArraySize>(buf: &mut [T]) -> (&mut [Array<T, N>], &mut [T]) {
    assert_ne!(N::USIZE, 0, "chunk size must be non-zero");
    // Arithmetic safety: we have checked that `N::USIZE` is not zero, thus
    // division always returns correct result. `tail_pos` can not be bigger than `buf.len()`,
    // thus overflow on multiplication and underflow on substraction are impossible.
    let chunks_len = buf.len() / N::USIZE;
    let tail_pos = N::USIZE * chunks_len;
    let tail_len = buf.len() - tail_pos;
    unsafe {
        let ptr = buf.as_mut_ptr();
        let chunks = slice::from_raw_parts_mut(ptr.cast(), chunks_len);
        let tail = slice::from_raw_parts_mut(ptr.add(tail_pos), tail_len);
        (chunks, tail)
    }
}
