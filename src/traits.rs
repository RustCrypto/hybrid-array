//! Trait definitions.

use crate::Array;
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
/// [`Self::Size::USIZE`]. Breaking this requirement will cause undefined behavior.
pub unsafe trait ArraySize: Sized + 'static {
    #[doc(hidden)]
    const __CHECK_INVARIANT: () = {
        let a = <Self::Size as Unsigned>::USIZE;
        let b = core::mem::size_of::<Self::ArrayType<u8>>();
        assert!(a == b, "ArraySize invariant violated");
    };

    /// The size underlying the array.
    type Size: Unsigned;

    /// Array type which corresponds to this size.
    ///
    /// This is always defined to be `[T; N]` where `N` is the same as
    /// [`ArraySize::Size::USIZE`][`typenum::Unsigned::USIZE`].
    type ArrayType<T>: AsRef<[T]>
        + AsMut<[T]>
        + Borrow<[T]>
        + BorrowMut<[T]>
        + From<Array<T, Self>>
        + Index<usize>
        + Index<Range<usize>>
        + IndexMut<usize>
        + IndexMut<Range<usize>>
        + Into<Array<T, Self>>
        + IntoIterator<Item = T>;
}

/// Associates an [`ArraySize`] with a given type.
pub trait AssocArraySize: Sized {
    /// Size of an array type, expressed as a [`typenum`]-based [`ArraySize`].
    type Size: ArraySize;
}

impl<T, U> AssocArraySize for Array<T, U>
where
    U: ArraySize,
{
    type Size = U;
}
