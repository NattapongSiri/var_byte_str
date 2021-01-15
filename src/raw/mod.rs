#[cfg(feature="serialize")]
use bitvec_serde::{boxed::BitBox, order::Lsb0, slice::BitSlice, vec::BitVec};
#[cfg(not(feature="serialize"))]
use bitvec::{boxed::BitBox, order::Lsb0, slice::BitSlice, vec::BitVec};

pub struct Borrowed<'a> {
    buffer: &'a [u8],
    sign: BitSlice<Lsb0, u8 >
}
pub struct BorrowGap {}