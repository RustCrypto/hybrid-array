/// Implement the `ArraySize` and `AssocArraySize` traits for a given list of `N => UN, ...`
/// mappings.
///
/// `N` is used over `UN::USIZE` in order to improve compile times (avoids associated constant
/// resolution)
macro_rules! impl_array_sizes {
    ($($len:expr => $ty:ident),+ $(,)?) => {
        $(
            unsafe impl crate::ArraySize for $ty {
                type ArrayType<T> = [T; $len];
            }

            impl<T> crate::AssocArraySize for [T; $len] {
                type Size = $ty;
            }
        )+
     };
}
pub(super) use impl_array_sizes;

/// Implement array sizes, also importing the relevant constants.
macro_rules! impl_array_sizes_with_import {
    ($($len:expr => $ty:ident),+ $(,)?) => {
        $(
            pub use typenum::consts::$ty;
            impl_array_sizes!($len => $ty);
        )+
     };
}
pub(super) use impl_array_sizes_with_import;

/// This macro constructs a UInt type from a sequence of bits.  The bits are interpreted as the
/// little-endian representation of the integer in question.  For example, uint!(1 1 0 1 0 0 1) is
/// U75 (not U105).
#[cfg(feature = "extra-sizes")]
macro_rules! uint {
    () => { typenum::UTerm };
    (0 $($bs:tt)*) => { typenum::UInt< uint!($($bs)*), typenum::B0 > };
    (1 $($bs:tt)*) => { typenum::UInt< uint!($($bs)*), typenum::B1 > };
}

#[cfg(feature = "extra-sizes")]
pub(super) use uint;
