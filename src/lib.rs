//! A variable byte encoded of gap to represent a string.
//! 
//! This crate is used mainly for large non English text that need to be represent by two or more
//! bytes per character in UTF-8 encoding. It encode string by iterating on each character
//! then turn it to `u32` then calculate distance of this `u32` to previous character.
//! The distance here is called `"gap"`. Each gap is compressed by using variable byte encoding scheme.
//! 
//! It assume that text is usually come in as cluster where many contiguous characters came have 
//! code point close to each other. In such case, the character is likely to take only single byte
//! with one extra bit for sign flag. See `README.md` for reason behind it.
//! 
//! In order to obtain back a character, it need to iterate from the very first character.
//! This is similar to typical UTF derivative encoding as each char may have different number of bytes.
//! 
//! In order to serialize the encoded string, feature flag `serialize` must be enable.
//! 
//! For example, in `cargo.toml`:
//! ```
//! var_byte_str = {version="*", features=["serialize"] default=false}
//! ```

#[cfg(feature="serialize")]
use bitvec_serde::{order::Lsb0, vec::BitVec};
#[cfg(not(feature="serialize"))]
use bitvec::{order::Lsb0, vec::BitVec};
use smallvec::SmallVec;

#[cfg(feature="serialize")]
use serde::{Deserialize, Serialize};

struct Encoder {
    value: u32,
}

impl Iterator for Encoder {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        match self.value {
            0 => None,
            // -64..=-1 => {
            //     let r = self.value + 192;
            //     self.value = 0;

            //     Some(r as u8)
            // },
            // -128..=-65 => {
            //     let r = self.value & 63;
            //     self.value >>= 6;
            //     Some(r as u8)
            // },
            // 1..=63 => {
            //     let r = self.value + 128;
            //     self.value = 0;

            //     Some(r as u8)
            // },
            // 64..=127 => {
            //     let r = self.value & 63;
            //     self.value >>= 6;

            //     Some(r as u8)
            // },
            1..=127 => {
                let r = self.value + 128;
                self.value = 0;

                Some(r as u8)
            },
            _ => {
                let r = self.value & 127;
                self.value >>= 7;

                Some(r as u8)
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (1, Some(4))
    }
}

impl core::iter::FusedIterator for Encoder {}

impl Encoder {
    #[inline]
    pub fn encode(value: u32) -> Encoder {
        Encoder {
            value,
        }
    }
}

/// The core struct that represent variable byte encoded of gap of string.
/// 
/// See [module documentation](index.html) for more detail
#[cfg(feature="serialize")]
#[derive(Debug)]
#[derive(Deserialize, Serialize)]
pub struct VarByteString {
    buffer: Vec<u8>,
    sign: BitVec<Lsb0, u8>
}

/// The core struct that represent variable byte encoded of gap of string.
/// 
/// See [module documentation](index.html) for more detail
#[cfg(not(feature="serialize"))]
#[derive(Debug)]
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
}

impl<'a> Into<String> for &'a VarByteString {
    fn into(self) -> String {
        let mut result = String::with_capacity(self.sign_len());
        self.chars().for_each(|c| {
            result.push(c);
        });
        result
    }
}

impl<'a> Into<String> for VarByteString {
    fn into(self) -> String {
        let mut result = String::with_capacity(self.sign_len());
        self.chars().for_each(|c| {
            result.push(c);
        });
        result
    }
}

impl core::fmt::Display for VarByteString {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let val : String = self.into();
        write!(f, "{}", val)
    }
}

impl<'a> From<&str> for VarByteString {
    fn from(s: &str) -> VarByteString {
        let mut chars = s.chars();
        let mut buffer = Vec::with_capacity(s.len());
        let mut sign = BitVec::with_capacity(s.len());

        if let Some(first) = chars.next() {
            let first = first as u32;
            Encoder::encode(first).for_each(|b| {
                buffer.push(b);
                sign.push(false);
            });
            chars.fold(first, |prev, c| {
                let c = c as u32;
                if c >= prev {
                    Encoder::encode(c - prev).for_each(|v| {
                        buffer.push(v);
                    });
                    sign.push(false);
                } else {
                    Encoder::encode(prev - c).for_each(|v| {
                        buffer.push(v);
                    });
                    sign.push(true);
                }
                // Encoder::encode(c - prev).for_each(|v| {
                //     buffer.push(v)
                // });

                // c as i64
                c as u32
            });
        }

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
        dbg!(var_bytes.size());
        let back : String = var_bytes.into();
        dbg!(val.len());
        assert_eq!(val, back.as_str());
    }

    #[test]
    fn display() {
        use core::fmt::Write as FmtWrite;
        let val = "Some value นะครับนะ";
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
}
