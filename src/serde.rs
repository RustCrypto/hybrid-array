//! Support for serializing and deserializing `Array` using `serde`.

use crate::{Array, ArraySize};
use core::{fmt, marker::PhantomData};
use serde::{
    de::{self, Deserialize, Deserializer, SeqAccess, Visitor},
    ser::{Serialize, SerializeTuple, Serializer},
};

impl<'de, T, U> Deserialize<'de> for Array<T, U>
where
    T: Deserialize<'de>,
    U: ArraySize,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
        T: Deserialize<'de>,
    {
        struct ArrayVisitor<T> {
            element: PhantomData<T>,
        }

        impl<'de, T, U> Visitor<'de> for ArrayVisitor<Array<T, U>>
        where
            T: Deserialize<'de>,
            U: ArraySize,
        {
            type Value = Array<T, U>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(formatter, "an array of length {}", U::USIZE)
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Array<T, U>, A::Error>
            where
                A: SeqAccess<'de>,
            {
                Array::<T, U>::try_from_fn(|i| {
                    seq.next_element()?
                        .ok_or_else(|| de::Error::invalid_length(i, &self))
                })
            }
        }

        let visitor = ArrayVisitor {
            element: PhantomData,
        };

        deserializer.deserialize_tuple(U::USIZE, visitor)
    }
}

impl<T, U> Serialize for Array<T, U>
where
    T: Serialize,
    U: ArraySize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_tuple(U::USIZE)?;

        for elem in self {
            seq.serialize_element(elem)?;
        }

        seq.end()
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    const INTEGER_ARRAY_EXAMPLE: [u64; 4] = [1, 2, 3, 4];
    use crate::{
        Array,
        sizes::{U4, U5},
    };
    use bincode::{
        config,
        error::DecodeError,
        serde::{decode_from_slice, encode_to_vec},
    };

    #[test]
    fn deserialize_integer_array() {
        let serialized = encode_to_vec(INTEGER_ARRAY_EXAMPLE, config::standard()).unwrap();
        let (deserialized, len): (Array<u64, U4>, usize) =
            decode_from_slice(&serialized, config::standard()).unwrap();

        assert_eq!(deserialized, INTEGER_ARRAY_EXAMPLE);
        assert_eq!(len, serialized.len());
    }

    #[test]
    fn deserialize_too_short() {
        let serialized = encode_to_vec(INTEGER_ARRAY_EXAMPLE, config::standard()).unwrap();
        let deserialized: Result<(Array<u8, U5>, usize), DecodeError> =
            decode_from_slice(&serialized, config::standard());

        // TODO(tarcieri): check for more specific error type
        assert!(deserialized.is_err())
    }

    #[test]
    fn serialize_integer_array() {
        let example: Array<u64, U4> = Array(INTEGER_ARRAY_EXAMPLE);
        let serialized = encode_to_vec(example, config::standard()).unwrap();
        let (deserialized, len): (Array<u64, U4>, usize) =
            decode_from_slice(&serialized, config::standard()).unwrap();

        assert_eq!(example, deserialized);
        assert_eq!(len, serialized.len());
    }
}
