//! A variable byte encoded of gap to represent a string.
//! 
//! This crate is used mainly for large non English text that need to be represent by two or more
//! bytes per character in UTF-8 encoding. It encode string by iterating on each character
//! then turn it to `u32` then calculate distance of this `u32` to previous character.
//! The distance here is called `"gap"`. Each gap is compressed by using variable byte encoding scheme.
//! 
//! It assume that text is usually come in as cluster where many contiguous characters came have 
//! code point close to each other. In such case, the character is likely to take only single byte
//! with one extra bit for sign flag. See [README.md](https://github.com/NattapongSiri/var_byte_str/blob/master/README.md) 
//! for reason behind it.
//! 
//! In order to obtain back a character, it need to iterate from the very first character.
//! This is similar to typical UTF derivative encoding as each char may have different number of bytes.
//! 
//! In order to serialize the encoded string, feature flag `serialize` must be enable.
//! 
//! For example, in `cargo.toml`:
//! ```toml
//! var_byte_str = {version="*", features=["serialize"] default=false}
//! ```

#[cfg(feature="serialize")]
use bitvec_serde::{order::Lsb0, vec::BitVec};
#[cfg(not(feature="serialize"))]
use bitvec::{order::Lsb0, vec::BitVec};
use smallvec::SmallVec;

#[cfg(feature="serialize")]
use serde::{Deserialize, Serialize};

/// Encoder that encode `u32` value into an encoded bytes.
/// This iterator return least significant byte first.
/// The last byte will contain a flag on 8th bit to discriminate
/// a most significant byte.
#[derive(Copy, Clone, Debug)]
struct LSBEncoder {
    /// Need to wrap value within `Option` so it can encode `0u32` too
    value: Option<u32>,
}

impl LSBEncoder {
    /// Create this encoder with given `u32` value.
    #[inline]
    pub fn encode(value: u32) -> LSBEncoder {
        LSBEncoder {
            value: Some(value),
        }
    }
}

impl Iterator for LSBEncoder {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(value) = self.value {
            match value {
                0..=127 => {
                    let r = value + 128;
                    self.value = None;

                    Some(r as u8)
                },
                _ => {
                    let r = value & 127;
                    self.value.replace(value >> 7);

                    Some(r as u8)
                }
            }
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let bits = 32 - self.value.map_or(32, |v| v.leading_zeros());
        let max = if bits > 0 {
            (bits + 6) / 7 // A round up integer div
        } else {
            0
        } as usize;
        (max, Some(max))
    }
}

/// Convert from LSBEncoder into MSBEncoder
impl From<MSBEncoder> for LSBEncoder {
    #[inline]
    fn from(e: MSBEncoder) -> LSBEncoder {
        LSBEncoder {
            value: e.value
        }
    }
}

impl ExactSizeIterator for LSBEncoder {}
impl core::iter::FusedIterator for LSBEncoder {}

/// Encoder that encode `u32` value into an encoded bytes similar to 
/// [LSBEncoder](struct.LSBEncoder.html) but return most significant byte first.
/// 
/// The first byte will be flagged byte. 8th bit will be 1 to discriminate a 
/// most significant byte.
/// 
/// It is expected that this encoder will be a bit slower than [LSBEncoder](struct.LSBEncoder.html)
/// due to nature of it that need to check on each iteration whether it should flag the byte
/// as MSB. This is not need with [LSBEncoder](struct.LSBEncoder.html) since only
/// last byte will have the flag.
#[derive(Copy, Clone, Debug)]
struct MSBEncoder {
    /// A flag so to check whether the most significant bit is already return
    flagged: bool,
    value: Option<u32>,
}

impl MSBEncoder {
    /// Create this encoder from given `u32` value.
    #[inline]
    pub fn encode(value: u32) -> MSBEncoder {
        MSBEncoder {
            flagged: false,
            value: Some(value)
        }
    }
}

impl Iterator for MSBEncoder {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(ref mut v) = self.value {
            let leading_0 = v.leading_zeros();
            match leading_0 {
                0..=3 => {
                    let result = if self.flagged {
                        Some(v.wrapping_shr(28) as u8)
                    } else {
                        self.flagged = true;
                        Some(128 + v.wrapping_shr(28) as u8)
                    };
                    *v &= 0b0000_1111_1111_1111_1111_1111_1111_1111;
                    result
                },
                4..=10 => {
                    let result = if self.flagged {
                        Some(v.wrapping_shr(21) as u8)
                    } else {
                        self.flagged = true;
                        Some(128 + v.wrapping_shr(21) as u8)
                    };
                    *v &= 0b0000_0000_0001_1111_1111_1111_1111_1111;
                    result
                },
                11..=17 => {
                    let result = if self.flagged {
                        Some(v.wrapping_shr(14) as u8)
                    } else {
                        self.flagged = true;
                        Some(128 + v.wrapping_shr(14) as u8)
                    };
                    *v &= 0b0000_0000_0000_0000_0011_1111_1111_1111;
                    result
                },
                18..=24 => {
                    let result = if self.flagged {
                        Some(v.wrapping_shr(7) as u8)
                    } else {
                        self.flagged = true;
                        Some(128 + v.wrapping_shr(7) as u8)
                    };
                    *v &= 0b0000_0000_0000_0000_0000_0000_0111_1111;
                    result
                },
                25..=31 => {
                    let result = if self.flagged {
                        Some(*v as u8)
                    } else {
                        self.flagged = true;
                        Some(128 + *v as u8)
                    };
                    self.value = None;
                    result
                },
                32 => {
                    self.value = None;
                    if self.flagged {
                        Some(0)
                    } else {
                        Some(128)
                    }
                },
                _ => {
                    // The code point is only `u32`, we'd have lesser than 32 bit
                    unreachable!()
                }
            }
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let bits = 32 - self.value.map_or(32, |v| v.leading_zeros());
        let max = if bits > 0 {
            (bits + 6) / 7 // A round up integer div
        } else {
            0
        } as usize;
        (max, Some(max))
    }
}
/// Convert from LSBEncoder into MSBEncoder
impl From<LSBEncoder> for MSBEncoder {
    #[inline]
    fn from(e: LSBEncoder) -> MSBEncoder {
        MSBEncoder {
            flagged: false,
            value: e.value
        }
    }
}

impl ExactSizeIterator for MSBEncoder {}
impl core::iter::FusedIterator for MSBEncoder {}

/// Encode other string based on chars into gaps.
/// 
/// On each iteration over this object, it yield an [LSBEncoder](struct.LSBEncoder.html) with
/// associated sign boolean.
struct CharsEncoder<'a> {
    prev: Option<u32>,
    chars: std::str::Chars<'a>
}

impl<'a> CharsEncoder<'a> {
    /// Construct an iterator that yield "variable bytes gap" encoded of each
    /// character in given `&str`
    #[inline]
    pub fn encode(s: &str) -> CharsEncoder {
        CharsEncoder {
            prev: None,
            chars: s.chars()
        }
    }
}

impl<'a> Iterator for CharsEncoder<'a> {
    type Item=(bool, LSBEncoder);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(c) = self.chars.next() {
            let c = c as u32;
            if let Some(p) = self.prev.replace(c) {
                if c < p {
                    Some((true, LSBEncoder::encode(p - c)))
                } else {
                    Some((false, LSBEncoder::encode(c - p)))
                }
            } else {
                Some((false, LSBEncoder::encode(c)))
            }
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.chars.size_hint()
    }
}
/// Encode other string based on chars into gaps.
/// 
/// On each iteration over this object, it yield an [LSBEncoder](struct.LSBEncoder.html) with
/// associated sign boolean.
#[derive(Debug)]
struct MSBCharsEncoder<'a> {
    prev: Option<u32>,
    chars: std::str::Chars<'a>
}

impl<'a> MSBCharsEncoder<'a> {
    /// Construct an iterator that yield "variable bytes encoded" gap of each character of
    /// given `&str`
    #[inline]
    pub fn encode(s: &str) -> MSBCharsEncoder {
        MSBCharsEncoder {
            prev: None,
            chars: s.chars()
        }
    }
}

impl<'a> Iterator for MSBCharsEncoder<'a> {
    type Item=(bool, MSBEncoder);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(c) = self.chars.next() {
            let c = c as u32;
            if let Some(p) = self.prev.replace(c) {
                if c < p {
                    Some((true, MSBEncoder::encode(p - c)))
                } else {
                    Some((false, MSBEncoder::encode(c - p)))
                }
            } else {
                Some((false, MSBEncoder::encode(c)))
            }
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.chars.size_hint()
    }
}

/// The core struct that represent variable byte encoded of gap of string.
/// 
/// See [module documentation](index.html) for more detail
#[cfg(feature="serialize")]
#[derive(Clone, Deserialize, Debug, Eq, Hash, Serialize)]
pub struct VarByteString {
    buffer: Vec<u8>,
    sign: BitVec<Lsb0, u8>
}

/// The core struct that represent variable byte encoded of gap of string.
/// 
/// See [module documentation](index.html) for more detail
#[cfg(not(feature="serialize"))]
#[derive(Clone, Debug, Eq, Hash)]
pub struct VarByteString {
    buffer: Vec<u8>,
    sign: BitVec<Lsb0, u8>
}

impl VarByteString {
    /// Return number of bytes of buffer that represent the string
    #[inline]
    pub fn buffer_len(&self) -> usize {
        self.buffer.len()
    }
    /// Return number of bit of `sign` that represent the string
    #[inline]
    pub fn sign_len(&self) -> usize {
        self.sign.len()
    }
    #[inline]
    pub fn len(&self) -> usize {
        self.buffer_len() + self.sign_len() / 8 + 1
    }
    /// Return number of bytes this object require to represent the string
    #[inline]
    pub fn size(&self) -> usize {
        (self.sign_len() / 8) + 1 + self.buffer_len() + core::mem::size_of::<BitVec<Lsb0, u8>>() + core::mem::size_of::<Vec<u8>>()
    }
    // pub fn sub_str<R>(&self, range: R) -> VarByteString where R: core::ops::RangeBounds<usize> {
    //     let start = match range.start_bound() {
    //         core::ops::Bound::Included(s) => *s,
    //         core::ops::Bound::Excluded(s) => *s + 1,
    //         core::ops::Bound::Unbounded => 0
    //     };
    //     let end = match range.end_bound() {
    //         core::ops::Bound::Included(e) => *e + 1,
    //         core::ops::Bound::Excluded(e) => *e,
    //         core::ops::Bound::Unbounded => 0
    //     };
    //     let buf_start = 0;
    //     let first_value = self.gaps().take(start).fold(0, |acc, gap| {
    //         buf_start +=1 ;
    //         acc + gap
    //     });
    //     let buffer = Vec::with_capacity(self.buffer_len() - buf_start);
    //     buffer.extend(Encoder::encode(first_value as u32));
    //     buffer.extend(self.buffer[buf_start..].iter());
    //     VarByteString {
    //         buffer,
    //         sign: self.sign[start..end]
    //     }
    // }
    /// Return an iterator of [chars](struct.Chars.html) where each iteration return
    /// a `char` primitive converted from this representation.
    #[inline]
    pub fn chars(&self) -> Chars {
        Chars {
            byte_cursor: 0,
            sign_cursor: 0,
            prev_char: 0,
            vbs: self
        }
    }
    /// Return an iterator of [gaps](struct.Gaps.html) where each iteration return a
    /// different between current character and previous character. The first iteration
    /// always return a code point. It return code point "as is" from original value.
    #[inline]
    pub fn gaps(&self) -> Gaps {
        Gaps {
            byte_cursor: 0,
            sign_cursor: 0,
            vbs: self
        }
    }
    /// Return an iterator of [bytes of gap](struct.GapsBytes.html) where each iteration
    /// return a tuple of `bool` and `SmallVec<[u8; 5]>`. The `bool` part is true when the
    /// bytes it represent should be convert to negative value. The `SmallVec<[u8; 5]>` part
    /// contain absolute value of different in least significant byte first order.
    #[inline]
    pub fn gaps_bytes(&self) -> GapsBytes {
        GapsBytes {
            byte_cursor: 0,
            sign_cursor: 0,
            vbs: self
        }
    }

    /// Find a common prefix between itself and other.
    /// 
    /// # Parameter
    /// - `other` - Any type `T` that can be convert into [VarByteString](struct.VarByteString.html)
    /// 
    /// # Return
    /// An number of characters where there's common prefix between itself and other. 
    /// The index is exclusive thus the prefix is within following range `0..index`
    pub fn prefix<T>(&self, other: T) -> usize where Self: From<T> {
        let other = Self::from(other);
        self.gaps_bytes().zip(other.gaps_bytes()).take_while(|(lhs, rhs)| 
            lhs.0 == rhs.0 && lhs.1 == rhs.1
        ).count()
    }

    /// Check if this string start with other given string.
    /// Return `true` if it is.
    /// 
    /// This is a subset operation of [prefix](struct.VarByteString.html#method.prefix)
    /// where entire other string must be prefix of this object.
    pub fn starts_with<T>(&self, other: T) -> bool where Self: From<T> {
        let other = Self::from(other);
        self.gaps_bytes().zip(other.gaps_bytes()).take_while(|(lhs, rhs)| 
            lhs.0 == rhs.0 && lhs.1 == rhs.1
        ).count() == other.sign.len()
    }
}

/// Add a way to convert back this object into `String`
impl<'a> Into<String> for &'a VarByteString {
    fn into(self) -> String {
        let mut result = String::with_capacity(self.sign_len());
        self.chars().for_each(|c| {
            result.push(c);
        });
        result
    }
}

/// Add a way to consume this object and turn it into `String`
impl<'a> Into<String> for VarByteString {
    fn into(self) -> String {
        let mut result = String::with_capacity(self.sign_len());
        self.chars().for_each(|c| {
            result.push(c);
        });
        result
    }
}

/// Specialize implementation of `PartialEq` by comparing sign bytes first.
/// It is more efficient than comparing absolute value of gap first as there is many more byte
/// to compare.
impl PartialEq for VarByteString {
    /// It compare with &str by encodes other string into variable gap bytes then compare it to self.
    fn eq(&self, other: &Self) -> bool {
        // It is much cheaper to compare sign bit as whole byte when
        // we want to compare every bit flag.
        self.sign.as_slice() == other.sign.as_slice() && self.buffer.as_slice() == other.buffer.as_slice()
    }
}

/// Allow [VarByteString](struct.VarByteString.html) to allow using operator `==` with `&str`
impl<S> core::cmp::PartialEq<S> for VarByteString where S: core::borrow::Borrow<str> {
    /// It compare with &str by encodes other string into variable gap bytes then compare it to self.
    fn eq(&self, other: &S) -> bool {
        // We can either encode other or decode self. Both operation is expensive.
        // Encode other may be less expensive as it may have less byte to compare.
        CharsEncoder::encode(other.borrow()).zip(self.gaps_bytes()).all(|(rhs, lhs)| {
            if rhs.0 == lhs.0 {
                rhs.1.eq(lhs.1)
            } else {
                false
            }
        })
    }
}

/// Allow [VarByteString](struct.VarByteString.html) to be comparable with `&str`
impl<S> core::cmp::PartialOrd<S> for VarByteString where S: core::borrow::Borrow<str> {
    /// It compare by encode other as `&str` into variable gap bytes and compare based on sign and bytes
    fn partial_cmp(&self, other: &S) -> Option<core::cmp::Ordering> {
        let mut var_bytes = self.gaps_bytes();
        let mut last_cmp = core::cmp::Ordering::Less;
        for (other_sign, other_encoded) in MSBCharsEncoder::encode(other.borrow()) {
            if let Some((sign, bytes)) = var_bytes.next() {
                if sign {
                    // self is signed
                    if other_sign {
                        // other is also signed

                        // Need to compare other to self so result is reversed.
                        // It is signed comparison, if it is self compare to other,
                        // result will need to be reversed. 
                        // Since it is already reverse, we return compare result as is.
                        last_cmp = if other_encoded.len() == bytes.len() {
                            other_encoded.cmp(bytes.into_iter().rev())
                        } else {
                            other_encoded.len().cmp(&bytes.len())
                        };

                        match last_cmp {
                            core::cmp::Ordering::Equal => (),
                            _ => break
                        }
                    } else {
                        last_cmp = core::cmp::Ordering::Less;
                        break
                    }
                } else {
                    // self is unsign
                    if other_sign {
                        // other is sign
                        last_cmp = core::cmp::Ordering::Greater;
                        break;
                    } else {
                        // other is also unsign
                        last_cmp = if other_encoded.len() == bytes.len() {
                            // Need to reverse result because we compare other to self.
                            // It is reverse comparison.
                            other_encoded.cmp(bytes.into_iter().rev()).reverse()
                        } else {
                            bytes.len().cmp(&other_encoded.len())
                        };

                        match last_cmp {
                            core::cmp::Ordering::Equal => (),
                            _ => break
                        }
                    }
                }
            } else {
                // self is exhausted while other is not and all prior comparison is equals
                last_cmp = core::cmp::Ordering::Less;
                break;
            }
        }
        Some(last_cmp)
    }
}

impl core::fmt::Display for VarByteString {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let val : String = self.into();
        write!(f, "{}", val)
    }
}

/// Add a way to construct this object from any kind of `str`
impl<S> From<S> for VarByteString where S: core::borrow::Borrow<str> {
    fn from(s: S) -> VarByteString {
        let s = s.borrow();
        let mut buffer = Vec::with_capacity(s.len());
        let mut sign = BitVec::with_capacity(s.len());

        CharsEncoder::encode(s).for_each(|(cur_sign, encoded)| {
            encoded.for_each(|v| {
                buffer.push(v);
            });
            sign.push(cur_sign);
        });

        VarByteString {
            buffer,
            sign
        }
    }
}

/// An iterator that return a `char` using unsafe cast.
/// 
/// This struct assume that the encoded came from valid Unicode code point.
/// Each iteration will calculate a code point based on encoded gap then cast
/// it directly to `char`
pub struct Chars<'a> {
    byte_cursor: usize,
    sign_cursor: usize,
    prev_char: u32,
    vbs: &'a VarByteString,
}

impl<'a> Iterator for Chars<'a> {
    type Item=char;

    fn next(&mut self) -> Option<Self::Item> {
        if self.byte_cursor >= self.vbs.buffer_len() {
            None
        } else {
            let mut pow = 0;
            let mut result : u32 = 0;
            for b in &self.vbs.buffer[self.byte_cursor..] {
                self.byte_cursor += 1;
                if *b < 128 {
                    result += (*b as u32) << pow;
                } else {
                    let diff = result + ((*b as u32 - 128) << pow);
                    if self.vbs.sign[self.sign_cursor] {
                        self.prev_char -= diff;
                    } else {
                        self.prev_char += diff;
                    }
                    self.sign_cursor += 1;
                    unsafe {
                        // It is safe to use unsafe here because all the bytes in the buffer came
                        // from valid code point
                        return Some(std::char::from_u32_unchecked(self.prev_char));
                    }
                }
                pow += 7;
            }

            None
        }
    }
}

impl<'a> core::iter::FusedIterator for Chars<'a> {}
impl<'a> core::iter::ExactSizeIterator for Chars<'a> {
    fn len(&self) -> usize {
        self.vbs.sign.len()
    }
}

/// An iterator that return gap of each character as `i64` offset.
/// The first return value can be cast to `char`. The subsequence
/// value need to be added to first value in order to obtain an `i64` that
/// can be cast to `char`.
///
/// This iterator doesn't check whether the return `i64` is safe to be cast
/// to `u32` or `char`. It assume that the gap is encoded from valid Unicode code point.
pub struct Gaps<'a> {
    byte_cursor: usize,
    sign_cursor: usize,
    vbs: &'a VarByteString,
}

impl<'a> Iterator for Gaps<'a> {
    type Item=i64;

    fn next(&mut self) -> Option<Self::Item> {
        if self.byte_cursor >= self.vbs.buffer_len() {
            None
        } else {
            let mut pow = 0;
            let mut result : i64 = 0;
            for b in &self.vbs.buffer[self.byte_cursor..] {
                self.byte_cursor += 1;
                if *b < 128 {
                    result += (*b as i64) << pow;
                } else {
                    let mut diff = result + ((*b as i64 - 128) << pow);
                    if self.vbs.sign[self.sign_cursor] {
                        diff *= -1;
                    } 
                    self.sign_cursor += 1;

                    return Some(diff)
                }
                pow += 7;
            }

            None
        }
    }
}

impl<'a> core::iter::FusedIterator for Gaps<'a> {}
impl<'a> core::iter::ExactSizeIterator for Gaps<'a> {
    fn len(&self) -> usize {
        self.vbs.sign.len()
    }
}

/// An iterator that return gap as copy of variable byte encoded along with sign boolean.
/// Each iteration return a tuple of `bool` and `SmallVec<[u8; 5]>`. The `bool` part is true when the
/// bytes it represent should be convert into negative value. The `SmallVec<[u8; 5]>` part
/// contain absolute value of different in least significant byte first order.
/// 
/// For example, if the different is 1. The return value will be (false, [1]). If the different is -1,
/// the return value will be (true, [1]).
/// 
/// It has the same assumption as [Gaps](struct.Gaps.html). It doesn't check validity of value.
pub struct GapsBytes<'a> {
    byte_cursor: usize,
    sign_cursor: usize,
    vbs: &'a VarByteString
}

impl<'a> Iterator for GapsBytes<'a> {
    /// Max number of bytes needed to store largest gap between two Unicode characters is 33 bits.
    /// Since variable byte encoding have 7 bits available per byte, so largest gap can be represent by 5 bytes.
    type Item = (bool, SmallVec<[u8; 5]>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.sign_cursor < self.vbs.sign_len() {
            let sign = self.vbs.sign[self.sign_cursor];
            self.sign_cursor += 1;

            let mut bytes = SmallVec::with_capacity(5);
            let len = self.vbs.buffer[self.byte_cursor..].iter().take_while(|b| **b < 128).fold(0, |acc, b| {
                bytes.push(*b);
                acc + 1
            });
            bytes.push(self.vbs.buffer[self.byte_cursor + len]);
            self.byte_cursor += len + 1;

            Some((sign, bytes))
        } else {
            None
        }
    }
}

impl<'a> core::iter::FusedIterator for GapsBytes<'a> {}
impl<'a> core::iter::ExactSizeIterator for GapsBytes<'a> {
    fn len(&self) -> usize {
        self.vbs.sign_len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use smallvec::smallvec;

    #[test]
    fn convert_back_forth() {
        let val = "Some value นะครับนะ";
        let var_bytes = VarByteString::from(val);
        let back : String = var_bytes.into();
        assert_eq!(val, back.as_str());
    }

    #[test]
    fn short_text_display() {
        use core::fmt::Write as FmtWrite;
        let val = "Some value นะครับนะ";
        let var_bytes = VarByteString::from(val);
        let mut disp = String::new();
        write!(&mut disp, "{}", var_bytes).unwrap();
        assert_eq!(val, disp);
    }
    #[test]
    fn long_text_display() {
        use core::fmt::Write as FmtWrite;
        let val = "Some really long text and may contains some different language like \"คำภาษาไทยที่ใช้พื้นที่เยอะกว่าเนื้อความภาษาอังกฤษเสียอีก\".";
        let var_bytes = VarByteString::from(val);
        let mut disp = String::new();
        write!(&mut disp, "{}", var_bytes).unwrap();
        assert_eq!(val, disp);
    }
    #[test]
    fn gaps() {
        let val = "abaกขa";
        let var_bytes = VarByteString::from(val);
        let expected = vec![b'a' as i64, 1, -1, 3488, 1, -3489];
        let gaps: Vec<i64> = var_bytes.gaps().collect();
        assert_eq!(expected, gaps);
    }
    #[test]
    fn gaps_bytes() {
        let val = "abaกขa";
        let var_bytes = VarByteString::from(val);
        let expected = vec![(false, smallvec!(b'a' + 128 as u8)), (false, smallvec![1 + 128]), (true, smallvec![1 + 128]), (false, smallvec![32, 27 + 128]), (false, smallvec![1 + 128]), (true, smallvec![33, 27 + 128])];
        let gaps: Vec<(bool, SmallVec<[u8; 5]>)> = var_bytes.gaps_bytes().collect();
        assert_eq!(expected, gaps);
    }
    #[test]
    fn msb_encode_int() {
        use smallvec::smallvec;
        let max: SmallVec<[u8; 5]> = smallvec![0b1000_1111, 127, 127, 127, 127];
        MSBEncoder::encode(u32::MAX).enumerate().for_each(|(i, byte)| {
            assert_eq!(byte, max[i]);
        });
        let min: SmallVec<[u8; 1]> = smallvec![128];
        MSBEncoder::encode(0).enumerate().for_each(|(i, byte)| {
            assert_eq!(byte, min[i]);
        });
        let imin: SmallVec<[u8; 5]> = smallvec![0b1000_0111, 127, 127, 127, 127];
        MSBEncoder::encode(i32::MAX as u32).enumerate().for_each(|(i, byte)| {
            assert_eq!(byte, imin[i]);
        });
        let one: SmallVec<[u8; 1]> = smallvec![0b1000_0001];
        MSBEncoder::encode(1).enumerate().for_each(|(i, byte)| {
            assert_eq!(byte, one[i]);
        });
        let thousand: SmallVec<[u8; 2]> = smallvec![0b1000_0111, 0b0110_1000];
        MSBEncoder::encode(1000).enumerate().for_each(|(i, byte)| {
            assert_eq!(byte, thousand[i]);
        });
        let hundredthousand: SmallVec<[u8; 3]> = smallvec![0b1000_0110, 0b0000_1101, 0b0010_0000];
        MSBEncoder::encode(100_000).enumerate().for_each(|(i, byte)| {
            assert_eq!(byte, hundredthousand[i]);
        });
        let tenmillion: SmallVec<[u8; 4]> = smallvec![0b1000_0100, 0b0110_0010, 0b0010_1101 ,0];
        MSBEncoder::encode(10_000_000).enumerate().for_each(|(i, byte)| {
            assert_eq!(byte, tenmillion[i]);
        });
    }

    #[test]
    fn eq_str() {
        let s = "abcba axa ทดสอบด้วยคำภาษาไทย";
        let not = "bbb";
        let vbs = VarByteString::from(s);
        assert_eq!(vbs, s);
        assert_ne!(vbs, not);
        assert_ne!(vbs, VarByteString::from(not));
        assert_eq!(vbs, VarByteString::from(s));
    }

    #[test]
    fn cmp_str() {
        let s1 = "abc";
        let s2 = "abd";
        let s3 = "bbc";
        let s5 = "กก ";
        let s6 = "ก ก";
        let s7 = " ก ก";
        let vbs = VarByteString::from(s1);
        assert!(vbs < s2);
        assert!(s3 > s1);
        assert_eq!(s1 > s3, false);
        assert!(s1 < s5);
        assert_eq!(s1 == s3, false);
        let thai_vbs = VarByteString::from(s5);
        assert!(thai_vbs > s1);
        assert!(thai_vbs > s2);
        assert!(thai_vbs > s3);
        assert!(thai_vbs == s5);
        assert!(thai_vbs > s6);
        assert!(thai_vbs > s7);
        assert!(vbs > s7);
    }

    #[test]
    fn hash_obj() {
        let original = "Some really long text and may contains some different language like \"คำภาษาไทยที่ใช้พื้นที่เยอะกว่าเนื้อความภาษาอังกฤษเสียอีก\".";
        let encoded = VarByteString::from(original);
        let mut hm = std::collections::HashMap::new();
        hm.insert(encoded.clone(), 1);
        assert_eq!(hm.get(&encoded), Some(&1));
    }

    #[test]
    fn prefix() {
        let first = "abcdefg";
        let second = "abcxyz";
        let encoded = VarByteString::from(first);
        assert_eq!(encoded.prefix(second), 3);
        let third = "xyz";
        assert_eq!(encoded.prefix(third), 0);
        let forth = "";
        assert_eq!(encoded.prefix(forth), 0);
        let thai_encoded = VarByteString::from("กรุงเทพฯ");
        assert_eq!(thai_encoded.prefix(first), 0);
        assert_eq!(thai_encoded.prefix("กรุงเทพมหานคร"), 7);
    }

    #[test]
    fn empty() {
        let empty = "";
        let encoded = VarByteString::from(empty);
        assert_eq!(encoded, "");
    }
}
