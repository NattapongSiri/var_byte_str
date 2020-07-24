use bitvec::vec::BitVec;
use bitvec::order::Lsb0;

#[cfg(feature="serde")]
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

#[cfg(feature="serde")]
#[derive(Debug)]
#[derive(Deserialize, Serialize)]
pub struct VarByteString {
    buffer: Vec<u8>,
    sign: BitVec<Lsb0, u8>
}

#[cfg(not(feature="serde"))]
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
    #[inline]
    pub fn chars(&self) -> Chars {
        Chars {
            byte_cursor: 0,
            sign_cursor: 0,
            prev_char: 0,
            vbs: self
        }
    }
    #[inline]
    pub fn gaps(&self) -> Gaps {
        Gaps {
            byte_cursor: 0,
            sign_cursor: 0,
            vbs: self
        }
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

#[cfg(test)]
mod tests {
    use super::*;

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
}
