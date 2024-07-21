use std::{
    borrow::{Borrow, BorrowMut},
    ops::{Index, IndexMut, Range},
};

use hybrid_array::Array;

struct CustomArray<T>([T; 54321]);
impl<T> AsRef<[T]> for CustomArray<T> {
    fn as_ref(&self) -> &[T] {
        &self.0
    }
}
impl<T> AsMut<[T]> for CustomArray<T> {
    fn as_mut(&mut self) -> &mut [T] {
        &mut self.0
    }
}
impl<T> Borrow<[T]> for CustomArray<T> {
    fn borrow(&self) -> &[T] {
        &self.0
    }
}
impl<T> BorrowMut<[T]> for CustomArray<T> {
    fn borrow_mut(&mut self) -> &mut [T] {
        &mut self.0
    }
}
impl<T> From<Array<T, Size54321>> for CustomArray<T> {
    fn from(value: Array<T, Size54321>) -> Self {
        value.0
    }
}
impl<T> From<CustomArray<T>> for Array<T, Size54321> {
    fn from(val: CustomArray<T>) -> Self {
        Array(val)
    }
}
impl<T> IntoIterator for CustomArray<T> {
    type Item = T;

    type IntoIter = std::array::IntoIter<T, 54321>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}
impl<T> Index<usize> for CustomArray<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}
impl<T> IndexMut<usize> for CustomArray<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}
impl<T> Index<Range<usize>> for CustomArray<T> {
    type Output = [T];

    fn index(&self, index: Range<usize>) -> &Self::Output {
        &self.0[index]
    }
}
impl<T> IndexMut<Range<usize>> for CustomArray<T> {
    fn index_mut(&mut self, index: Range<usize>) -> &mut Self::Output {
        &mut self.0[index]
    }
}

struct Size54321;

// This macro constructs a UInt type from a sequence of bits.  The bits are interpreted as the
// little-endian representation of the integer in question.  For example, uint!(1 1 0 1 0 0 1) is
// U75 (not U105).
macro_rules! uint {
    () => { typenum::UTerm };
    (0 $($bs:tt)*) => { typenum::UInt< uint!($($bs)*), typenum::B0 > };
    (1 $($bs:tt)*) => { typenum::UInt< uint!($($bs)*), typenum::B1 > };
}

unsafe impl hybrid_array::ArraySize for Size54321 {
    type Size = uint!(1 0 0 0 1 1 0 0 0 0 1 0 1 0 1 1);
    type ArrayType<T> = CustomArray<T>;
}

#[test]
fn from_fn() {
    let array = Array::<u8, Size54321>::from_fn(|n| (n + 1) as u8);
    assert_eq!(array.as_slice().len(), 54321);
}
