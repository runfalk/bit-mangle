use crate::BufferExhausted;

#[derive(Debug)]
pub struct Cursor<'a> {
    buf: &'a [u8],
    offset: usize,
}

impl<'a> Cursor<'a> {
    /// Create a cursor from an immutble slice.
    ///
    /// This is used for decoding data.
    pub fn from_slice(buf: &'a [u8]) -> Self {
        Self { buf, offset: 0 }
    }

    /// Remaining bits in buffer
    pub fn bit_len(&self) -> usize {
        self.buf.len() * 8 - self.offset
    }

    /// Return which byte the cursor is currently at.
    pub fn byte_offset(&self) -> usize {
        self.offset / 8
    }

    /// Give the bit offset relative to the current byte of the cursor.
    pub fn bit_offset(&self) -> usize {
        self.offset % 8
    }

    /// Set the cursor to the given bit index.
    pub fn seek(&mut self, bit: usize) -> Result<(), BufferExhausted> {
        if bit > self.bit_len() {
            return Err(BufferExhausted);
        }
        self.offset = bit;
        Ok(())
    }

    /// Advance the cursor by the given number of bits.
    pub fn skip(&mut self, bits: usize) -> Result<(), BufferExhausted> {
        if bits > self.bit_len() {
            return Err(BufferExhausted);
        }
        self.offset += bits;
        Ok(())
    }

    fn peek_u8(&self) -> u8 {
        let offset = self.bit_offset() as u32;
        let high = self
            .buf
            .get(self.byte_offset())
            .copied()
            .unwrap_or(0)
            .checked_shl(offset)
            .unwrap_or(0);
        let low = self
            .buf
            .get(self.byte_offset() + 1)
            .copied()
            .unwrap_or(0)
            .checked_shr(8 - offset)
            .unwrap_or(0);
        high | low
    }

    fn peek_be_u16(&self) -> u16 {
        let high = self.peek_u8();
        let low = Cursor {
            buf: self.buf,
            offset: self.offset + 8,
        }
        .peek_u8();
        u16::from_be_bytes([high, low])
    }

    fn peek_be_u32(&self) -> u32 {
        let high = self.peek_be_u16() as u32;
        let low = if self.buf.len() > 1 {
            Cursor {
                buf: self.buf,
                offset: self.offset + 16,
            }
            .peek_be_u16() as u32
        } else {
            0
        };
        high << 16 | low
    }

    pub fn decode_bool(&mut self) -> Result<bool, BufferExhausted> {
        self.decode_u1().map(|n| n > 0)
    }
}

macro_rules! impl_decode_u8 {
    ($method_name:ident, $bits:literal) => {
        impl<'a> Cursor<'a> {
            /// Decode the given number of bits and advance the cursor.
            ///
            /// Network byte order (big endian) is assumed.
            pub fn $method_name(&mut self) -> Result<u8, BufferExhausted> {
                let num = self.peek_u8() >> 8 - $bits;
                self.skip($bits)?;
                Ok(num)
            }
        }
    };
}

macro_rules! impl_decode_i8 {
    ($method_name:ident, $bits:literal) => {
        impl<'a> Cursor<'a> {
            /// Decode the given number of bits and advance the cursor.
            ///
            /// Twos complement and network byte order (big endian) is assumed.
            pub fn $method_name(&mut self) -> Result<i8, BufferExhausted> {
                let bits = $bits;
                let num = self.peek_u8() >> 8 - bits;
                self.skip(bits)?;
                let is_neg = num & (1 << (bits - 1)) > 0;
                if is_neg && bits < 8 {
                    // We rely on that rust uses twos complement internally
                    Ok(((0xffu8 << bits) | num) as i8)
                } else {
                    Ok(num as i8)
                }
            }
        }
    };
}

macro_rules! impl_decode_u16 {
    ($method_name:ident, $bits:literal) => {
        impl<'a> Cursor<'a> {
            pub fn $method_name(&mut self) -> Result<u16, BufferExhausted> {
                let num = self.peek_be_u16() >> 16 - $bits;
                self.skip($bits)?;
                Ok(num)
            }
        }
    };
}

macro_rules! impl_decode_i16 {
    ($method_name:ident, $bits:literal) => {
        impl<'a> Cursor<'a> {
            pub fn $method_name(&mut self) -> Result<i16, BufferExhausted> {
                let bits = $bits;
                let num = self.peek_be_u16() >> 16 - bits;
                self.skip(bits)?;
                let is_neg = num & (1 << (bits - 1)) > 0;
                if is_neg && bits < 16 {
                    // We rely on that rust uses twos complement internally
                    Ok(((0xffffu16 << bits) | num) as i16)
                } else {
                    Ok(num as i16)
                }
            }
        }
    };
}

macro_rules! impl_decode_u32 {
    ($method_name:ident, $bits:literal) => {
        impl<'a> Cursor<'a> {
            pub fn $method_name(&mut self) -> Result<u32, BufferExhausted> {
                let num = self.peek_be_u32() >> 32 - $bits;
                self.skip($bits)?;
                Ok(num)
            }
        }
    };
}

macro_rules! impl_decode_i32 {
    ($method_name:ident, $bits:literal) => {
        impl<'a> Cursor<'a> {
            pub fn $method_name(&mut self) -> Result<i32, BufferExhausted> {
                let bits = $bits;
                let num = self.peek_be_u32() >> 32 - $bits;
                self.skip(bits)?;
                let is_neg = num & (1 << (bits - 1)) > 0;
                if is_neg && bits < 32 {
                    // We rely on that rust uses twos complement internally
                    Ok(((0xffff_ffffu32 << bits) | num) as i32)
                } else {
                    Ok(num as i32)
                }
            }
        }
    };
}

impl_decode_u8!(decode_u1, 1);
impl_decode_u8!(decode_u2, 2);
impl_decode_u8!(decode_u3, 3);
impl_decode_u8!(decode_u4, 4);
impl_decode_u8!(decode_u5, 5);
impl_decode_u8!(decode_u6, 6);
impl_decode_u8!(decode_u7, 7);
impl_decode_u8!(decode_u8, 8);

impl_decode_u16!(decode_u9, 9);
impl_decode_u16!(decode_u10, 10);
impl_decode_u16!(decode_u11, 11);
impl_decode_u16!(decode_u12, 12);
impl_decode_u16!(decode_u13, 13);
impl_decode_u16!(decode_u14, 14);
impl_decode_u16!(decode_u15, 15);
impl_decode_u16!(decode_u16, 16);

impl_decode_u32!(decode_u17, 17);
impl_decode_u32!(decode_u18, 18);
impl_decode_u32!(decode_u19, 19);
impl_decode_u32!(decode_u20, 20);
impl_decode_u32!(decode_u21, 21);
impl_decode_u32!(decode_u22, 22);
impl_decode_u32!(decode_u23, 23);
impl_decode_u32!(decode_u24, 24);
impl_decode_u32!(decode_u25, 25);
impl_decode_u32!(decode_u26, 26);
impl_decode_u32!(decode_u27, 27);
impl_decode_u32!(decode_u28, 28);
impl_decode_u32!(decode_u29, 29);
impl_decode_u32!(decode_u30, 30);
impl_decode_u32!(decode_u31, 31);
impl_decode_u32!(decode_u32, 32);

impl_decode_i8!(decode_i2, 2);
impl_decode_i8!(decode_i3, 3);
impl_decode_i8!(decode_i4, 4);
impl_decode_i8!(decode_i5, 5);
impl_decode_i8!(decode_i6, 6);
impl_decode_i8!(decode_i7, 7);
impl_decode_i8!(decode_i8, 8);

impl_decode_i16!(decode_i9, 9);
impl_decode_i16!(decode_i10, 10);
impl_decode_i16!(decode_i11, 11);
impl_decode_i16!(decode_i12, 12);
impl_decode_i16!(decode_i13, 13);
impl_decode_i16!(decode_i14, 14);
impl_decode_i16!(decode_i15, 15);
impl_decode_i16!(decode_i16, 16);

impl_decode_i32!(decode_i17, 17);
impl_decode_i32!(decode_i18, 18);
impl_decode_i32!(decode_i19, 19);
impl_decode_i32!(decode_i20, 20);
impl_decode_i32!(decode_i21, 21);
impl_decode_i32!(decode_i22, 22);
impl_decode_i32!(decode_i23, 23);
impl_decode_i32!(decode_i24, 24);
impl_decode_i32!(decode_i25, 25);
impl_decode_i32!(decode_i26, 26);
impl_decode_i32!(decode_i27, 27);
impl_decode_i32!(decode_i28, 28);
impl_decode_i32!(decode_i29, 29);
impl_decode_i32!(decode_i30, 30);
impl_decode_i32!(decode_i31, 31);
impl_decode_i32!(decode_i32, 32);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bit_len_and_skip() {
        let buf = [0u8; 10];

        assert_eq!(Cursor::from_slice(&buf).bit_len(), 80);
        assert_eq!(Cursor::from_slice(&buf[..5]).bit_len(), 40);

        let mut offset_buf = Cursor::from_slice(&buf);
        offset_buf.skip(7).unwrap();
        assert_eq!(offset_buf.bit_len(), 73);
        offset_buf.skip(2).unwrap();
        assert_eq!(offset_buf.bit_len(), 71);

        assert_eq!(offset_buf.skip(72), Err(BufferExhausted));
    }

    #[test]
    fn test_buffer_underflow() {
        let buf = [0xffu8];
        let mut cursor = Cursor::from_slice(&buf);
        cursor.skip(1).unwrap();

        // Try all decoding functions that exhaust the buffer
        assert_eq!(cursor.decode_u8(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u9(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u10(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u11(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u12(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u13(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u14(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u15(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u16(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u17(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u18(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u19(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u20(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u21(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u22(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u23(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u24(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u25(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u26(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u27(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u28(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u29(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u30(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u31(), Err(BufferExhausted));
        assert_eq!(cursor.decode_u32(), Err(BufferExhausted));

        // Ensure that the buffer was never advanced accidentally
        assert_eq!(cursor.decode_u7(), Ok(127));
    }

    #[test]
    fn test_decode_u1() {
        let buf = [0b1010_1010u8];
        let mut cursor = Cursor::from_slice(&buf);

        assert_eq!(cursor.decode_u1(), Ok(1));
        assert_eq!(cursor.decode_u1(), Ok(0));
        assert_eq!(cursor.decode_u1(), Ok(1));
        assert_eq!(cursor.decode_u1(), Ok(0));
        assert_eq!(cursor.decode_u1(), Ok(1));
        assert_eq!(cursor.decode_u1(), Ok(0));
        assert_eq!(cursor.decode_u1(), Ok(1));
        assert_eq!(cursor.decode_u1(), Ok(0));

        assert_eq!(cursor.bit_len(), 0);

        let buf = [0b1111_0000u8];
        let mut cursor = Cursor::from_slice(&buf);

        assert_eq!(cursor.decode_u1(), Ok(1));
        assert_eq!(cursor.decode_u1(), Ok(1));
        assert_eq!(cursor.decode_u1(), Ok(1));
        assert_eq!(cursor.decode_u1(), Ok(1));
        assert_eq!(cursor.decode_u1(), Ok(0));
        assert_eq!(cursor.decode_u1(), Ok(0));
        assert_eq!(cursor.decode_u1(), Ok(0));
        assert_eq!(cursor.decode_u1(), Ok(0));

        assert_eq!(cursor.bit_len(), 0);
    }

    #[test]
    fn test_decode_u2() {
        let buf = [1u8, 0b1000_0000];
        let mut cursor = Cursor::from_slice(&buf);

        cursor.skip(7).unwrap();
        assert_eq!(cursor.decode_u2(), Ok(0b11));
        assert_eq!(cursor.bit_len(), 7);
    }

    #[test]
    fn test_decode_u3() {
        let buf = [0b10u8, 0b1000_0000];
        let mut cursor = Cursor::from_slice(&buf);

        cursor.skip(6).unwrap();
        assert_eq!(cursor.decode_u3(), Ok(0b101));
        assert_eq!(cursor.bit_len(), 7);
    }

    #[test]
    fn test_decode_u4() {
        let buf = [0b100u8, 0b1000_0000];
        let mut cursor = Cursor::from_slice(&buf);

        cursor.skip(5).unwrap();
        assert_eq!(cursor.decode_u4(), Ok(0b1001));
        assert_eq!(cursor.bit_len(), 7);
    }

    #[test]
    fn test_decode_u5() {
        let buf = [0b1000u8, 0b1000_0000];
        let mut cursor = Cursor::from_slice(&buf);

        cursor.skip(4).unwrap();
        assert_eq!(cursor.decode_u5(), Ok(0b1_0001));
        assert_eq!(cursor.bit_len(), 7);
    }

    #[test]
    fn test_decode_u6() {
        let buf = [0b1_0000u8, 0b1000_0000];
        let mut cursor = Cursor::from_slice(&buf);

        cursor.skip(3).unwrap();
        assert_eq!(cursor.decode_u6(), Ok(0b10_0001));
        assert_eq!(cursor.bit_len(), 7);
    }

    #[test]
    fn test_decode_u7() {
        let buf = [0b10_0000u8, 0b1000_0000];
        let mut cursor = Cursor::from_slice(&buf);

        cursor.skip(2).unwrap();
        assert_eq!(cursor.decode_u7(), Ok(0b100_0001));
        assert_eq!(cursor.bit_len(), 7);
    }

    #[test]
    fn test_decode_u8() {
        let buf = [0b100_0000u8, 0b1000_0000];
        let mut cursor = Cursor::from_slice(&buf);

        cursor.skip(1).unwrap();
        assert_eq!(cursor.decode_u8(), Ok(0b1000_0001));
        assert_eq!(cursor.bit_len(), 7);
    }

    #[test]
    fn test_decode_u9() {
        let buf = [0b100_0000u8, 0b0100_0000];
        let mut cursor = Cursor::from_slice(&buf);

        cursor.skip(1).unwrap();
        assert_eq!(cursor.decode_u9(), Ok(0b1_0000_0001));
        assert_eq!(cursor.bit_len(), 6);
    }
}
