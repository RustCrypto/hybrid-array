use super::{impl_array_sizes, uint};

// SLH-DSA sizes
pub type U7856 = uint!(0 0 0 0 1 1 0 1 0 1 1 1 1);
pub type U16224 = uint!(0 0 0 0 0 1 1 0 1 1 1 1 1 1);
pub type U17088 = uint!(0 0 0 0 0 0 1 1 0 1 0 0 0 0 1);
pub type U29792 = uint!(0 0 0 0 0 1 1 0 0 0 1 0 1 1 1);
pub type U35664 = uint!(0 0 0 0 1 0 1 0 1 1 0 1 0 0 0 1);
pub type U49856 = uint!(0 0 0 0 0 0 1 1 0 1 0 0 0 0 1 1);

// SLH-DSA sizes
impl_array_sizes! {
    7856 => U7856,
    16224 => U16224,
    17088 => U17088,
    29792 => U29792,
    35664 => U35664,
    49856 => U49856,
}
