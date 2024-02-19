//! Macros for defining various array sizes, and their associated invocations.

use super::{ArraySize, AssocArraySize};
use typenum::{consts::*, Unsigned};

/// Additional typenum size aliases beyond what are normally provided.
///
/// These are defined using their component bits rather than `Add` to avoid conflicting impls.
pub mod extra_sizes {
    use typenum::{UInt, UTerm, B0, B1};

    // This macro constructs a UInt type from a sequence of bits.  The bits are interpreted as the
    // little-endian representation of the integer in question.  For example, uint!(1 1 0 1 0 0 1) is
    // U75 (not U105).
    macro_rules! uint {
        () => { UTerm };
        (0 $($bs:tt)*) => { UInt< uint!($($bs)*), B0 > };
        (1 $($bs:tt)*) => { UInt< uint!($($bs)*), B1 > };
    }

    pub type U1088 = uint!(0 0 0 0 0 0 1 0 0 0 1  );
    pub type U1152 = uint!(0 0 0 0 0 0 0 1 0 0 1  );
    pub type U1184 = uint!(0 0 0 0 0 1 0 1 0 0 1  );
    pub type U1408 = uint!(0 0 0 0 0 0 0 1 1 0 1  );
    pub type U1472 = uint!(0 0 0 0 0 0 1 1 1 0 1  );
    pub type U1536 = uint!(0 0 0 0 0 0 0 0 0 1 1  );
    pub type U1568 = uint!(0 0 0 0 0 1 0 0 0 1 1  );
    pub type U1600 = uint!(0 0 0 0 0 0 1 0 0 1 1  );
    pub type U1632 = uint!(0 0 0 0 0 1 1 0 0 1 1  );
    pub type U2336 = uint!(0 0 0 0 0 1 0 0 1 0 0 1);
    pub type U2368 = uint!(0 0 0 0 0 0 1 0 1 0 0 1);
    pub type U2400 = uint!(0 0 0 0 0 1 1 0 1 0 0 1);
    pub type U3072 = uint!(0 0 0 0 0 0 0 0 0 0 1 1);
    pub type U3104 = uint!(0 0 0 0 0 1 0 0 0 0 1 1);
    pub type U3136 = uint!(0 0 0 0 0 0 1 0 0 0 1 1);
    pub type U3168 = uint!(0 0 0 0 0 1 1 0 0 0 1 1);
}

pub use extra_sizes::*;

macro_rules! impl_array_size {
    ($($ty:ty),+ $(,)?) => {
        $(
            unsafe impl ArraySize for $ty {
                type ArrayType<T> = [T; <$ty as Unsigned>::USIZE];
            }

            impl<T> AssocArraySize for [T; <$ty as Unsigned>::USIZE] {
                type Size = $ty;
            }
        )+
     };
}

impl_array_size! {
    U0,
    U1,
    U2,
    U3,
    U4,
    U5,
    U6,
    U7,
    U8,
    U9,
    U10,
    U11,
    U12,
    U13,
    U14,
    U15,
    U16,
    U17,
    U18,
    U19,
    U20,
    U21,
    U22,
    U23,
    U24,
    U25,
    U26,
    U27,
    U28,
    U29,
    U30,
    U31,
    U32,
    U33,
    U34,
    U35,
    U36,
    U37,
    U38,
    U39,
    U40,
    U41,
    U42,
    U43,
    U44,
    U45,
    U46,
    U47,
    U48,
    U49,
    U50,
    U51,
    U52,
    U53,
    U54,
    U55,
    U56,
    U57,
    U58,
    U59,
    U60,
    U61,
    U62,
    U63,
    U64,
    U65,
    U66,
    U67,
    U68,
    U69,
    U70,
    U71,
    U72,
    U73,
    U74,
    U75,
    U76,
    U77,
    U78,
    U79,
    U80,
    U81,
    U82,
    U83,
    U84,
    U85,
    U86,
    U87,
    U88,
    U89,
    U90,
    U91,
    U92,
    U93,
    U94,
    U95,
    U96,
    U97,
    U98,
    U99,
    U100,
    U101,
    U102,
    U103,
    U104,
    U105,
    U106,
    U107,
    U108,
    U109,
    U110,
    U111,
    U112,
    U113,
    U114,
    U115,
    U116,
    U117,
    U118,
    U119,
    U120,
    U121,
    U122,
    U123,
    U124,
    U125,
    U126,
    U127,
    U128,
    U129,
    U130,
    U131,
    U132,
    U133,
    U134,
    U135,
    U136,
    U137,
    U138,
    U139,
    U140,
    U141,
    U142,
    U143,
    U144,
    U145,
    U146,
    U147,
    U148,
    U149,
    U150,
    U151,
    U152,
    U153,
    U154,
    U155,
    U156,
    U157,
    U158,
    U159,
    U160,
    U161,
    U162,
    U163,
    U164,
    U165,
    U166,
    U167,
    U168,
    U169,
    U170,
    U171,
    U172,
    U173,
    U174,
    U175,
    U176,
    U177,
    U178,
    U179,
    U180,
    U181,
    U182,
    U183,
    U184,
    U185,
    U186,
    U187,
    U188,
    U189,
    U190,
    U191,
    U192,
    U193,
    U194,
    U195,
    U196,
    U197,
    U198,
    U199,
    U200,
    U201,
    U202,
    U203,
    U204,
    U205,
    U206,
    U207,
    U208,
    U209,
    U210,
    U211,
    U212,
    U213,
    U214,
    U215,
    U216,
    U217,
    U218,
    U219,
    U220,
    U221,
    U222,
    U223,
    U224,
    U225,
    U226,
    U227,
    U228,
    U229,
    U230,
    U231,
    U232,
    U233,
    U234,
    U235,
    U236,
    U237,
    U238,
    U239,
    U240,
    U241,
    U242,
    U243,
    U244,
    U245,
    U246,
    U247,
    U248,
    U249,
    U250,
    U251,
    U252,
    U253,
    U254,
    U255,
    U256,
    U272,
    U288,
    U304,
    U320,
    U336,
    U352,
    U368,
    U384,
    U400,
    U416,
    U432,
    U448,
    U464,
    U480,
    U496,
    U512,
    U528,
    U544,
    U560,
    U576,
    U592,
    U608,
    U624,
    U640,
    U656,
    U672,
    U688,
    U704,
    U720,
    U736,
    U752,
    U768,
    U784,
    U800,
    U816,
    U832,
    U848,
    U864,
    U880,
    U896,
    U912,
    U928,
    U944,
    U960,
    U976,
    U992,
    U1008,
    U1024,
    U1088,
    U1152,
    U1184,
    U1408,
    U1472,
    U1536,
    U1568,
    U1600,
    U1632,
    U2048,
    U2336,
    U2368,
    U2400,
    U3072,
    U3104,
    U3136,
    U3168,
    U4096,
}
