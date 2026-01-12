//! Support for serializing and deserializing `Array` using wincode.

use crate::{Array, ArraySize};
use core::mem;
use core::mem::MaybeUninit;
use core::mem::transmute;
use wincode::ReadResult;
use wincode::SchemaRead;
use wincode::SchemaWrite;
use wincode::TypeMeta;
use wincode::WriteResult;
use wincode::ZeroCopy;
use wincode::io::Reader;
use wincode::io::Writer;

pub(crate) struct SliceDropGuard<T> {
    ptr: *mut MaybeUninit<T>,
    initialized_len: usize,
}

impl<T> SliceDropGuard<T> {
    pub(crate) fn new(ptr: *mut MaybeUninit<T>) -> Self {
        Self {
            ptr,
            initialized_len: 0,
        }
    }

    #[inline(always)]
    #[allow(clippy::arithmetic_side_effects)]
    pub(crate) fn inc_len(&mut self) {
        self.initialized_len += 1;
    }
}

impl<T> Drop for SliceDropGuard<T> {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe {
            core::ptr::drop_in_place(core::ptr::slice_from_raw_parts_mut(
                self.ptr.cast::<T>(),
                self.initialized_len,
            ));
        }
    }
}

// SAFETY:
// - Array<T, U> where T: ZeroCopy is trivially zero-copy. The length is constant,
//   so there is no length encoding.
unsafe impl<T, U: ArraySize> ZeroCopy for Array<T, U> where T: ZeroCopy {}

impl<'de, T, U> SchemaRead<'de> for Array<T, U>
where
    T: SchemaRead<'de>,
    U: ArraySize,
{
    type Dst = Array<T::Dst, U>;

    const TYPE_META: TypeMeta = const {
        match T::TYPE_META {
            TypeMeta::Static { size, zero_copy } => TypeMeta::Static {
                size: U::USIZE * size,
                zero_copy,
            },
            TypeMeta::Dynamic => TypeMeta::Dynamic,
        }
    };

    #[inline]
    fn read(reader: &mut impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
        if let TypeMeta::Static {
            zero_copy: true, ..
        } = T::TYPE_META
        {
            // SAFETY: `T::Dst` is zero-copy eligible (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
            unsafe { reader.copy_into_t(dst)? };
            return Ok(());
        }

        // SAFETY: MaybeUninit<Array<T::Dst, U>> trivially converts to Array<MaybeUninit<T::Dst>, U>.
        let dst = unsafe {
            transmute::<&mut MaybeUninit<Self::Dst>, &mut Array<MaybeUninit<T::Dst>, U>>(dst)
        };
        let base = dst.as_mut_ptr();
        let mut guard = SliceDropGuard::<T::Dst>::new(base);
        if let TypeMeta::Static { size, .. } = Self::TYPE_META {
            // SAFETY: `Self::TYPE_META` specifies a static size, which is `U::USIZE * static_size_of(T)`.
            // `U::USIZE reads of `T` will consume `size` bytes, fully consuming the trusted window.
            let reader = &mut unsafe { reader.as_trusted_for(size) }?;
            for i in 0..U::USIZE {
                let slot = unsafe { &mut *base.add(i) };
                T::read(reader, slot)?;
                guard.inc_len();
            }
        } else {
            for i in 0..U::USIZE {
                let slot = unsafe { &mut *base.add(i) };
                T::read(reader, slot)?;
                guard.inc_len();
            }
        }
        mem::forget(guard);
        Ok(())
    }
}

impl<T, U> SchemaWrite for Array<T, U>
where
    T: SchemaWrite,
    T::Src: Sized,
    U: ArraySize,
{
    type Src = Array<T::Src, U>;

    const TYPE_META: TypeMeta = const {
        match T::TYPE_META {
            TypeMeta::Static { size, zero_copy } => TypeMeta::Static {
                size: U::USIZE * size,
                zero_copy,
            },
            TypeMeta::Dynamic => TypeMeta::Dynamic,
        }
    };

    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    fn size_of(value: &Self::Src) -> WriteResult<usize> {
        if let TypeMeta::Static { size, .. } = Self::TYPE_META {
            return Ok(size);
        }
        // Extremely unlikely a type-in-memory's size will overflow usize::MAX.
        value
            .iter()
            .map(T::size_of)
            .try_fold(0usize, |acc, x| x.map(|x| acc + x))
    }

    #[inline]
    fn write(writer: &mut impl Writer, value: &Self::Src) -> WriteResult<()> {
        match Self::TYPE_META {
            TypeMeta::Static {
                zero_copy: true, ..
            } => {
                // SAFETY: `T::Src` is zero-copy eligible (no invalid bit patterns, no layout requirements, no endianness checks, etc.).
                unsafe { writer.write_slice_t(value)? };
            }
            TypeMeta::Static {
                size,
                zero_copy: false,
            } => {
                // SAFETY: `Self::TYPE_META` specifies a static size, which is `U::USIZE * static_size_of(T)`.
                // `U::USIZE` writes of `T` will write `size` bytes, fully initializing the trusted window.
                let writer = &mut unsafe { writer.as_trusted_for(size) }?;
                for item in value {
                    T::write(writer, item)?;
                }
                writer.finish()?;
            }
            TypeMeta::Dynamic => {
                for item in value {
                    T::write(writer, item)?;
                }
            }
        }

        Ok(())
    }
}
