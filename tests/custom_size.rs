use hybrid_array::Array;

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
    type ArrayType<T> = [T; 54321];
}

#[test]
fn from_fn() {
    let array = Array::<u8, Size54321>::from_fn(|n| (n + 1) as u8);
    assert_eq!(array.as_slice().len(), 54321);
}
