use crate::BufferExhausted;

#[derive(Debug)]
pub struct MutCursor<'a> {
    buf: &'a mut [u8],
    offset: usize,
}

impl<'a> MutCursor<'a> {
    /// Create a mutable cursor from an mutable slice.
    ///
    /// This is used for encoding data.
    pub fn from_slice(buf: &'a mut [u8]) -> Self {
        Self { buf, offset: 0 }
    }

    /// Total number of bits in buffer (includes consumed bits)
    pub fn bit_len(&self) -> usize {
        self.buf.len() * 8
    }

    /// Remaining bits in buffer
    pub fn bits_rem(&self) -> usize {
        self.bit_len() - self.offset
    }

    /// Return which byte the cursor is currently at.
    pub fn byte_offset(&self) -> usize {
        self.offset / 8
    }

    /// The offset from the start of the buffer in bits.
    pub fn bit_offset(&self) -> usize {
        self.offset
    }

    /// Set the cursor to the given bit index.
    pub fn seek(&mut self, bit: usize) -> Result<(), BufferExhausted> {
        if bit >= self.bit_len() {
            return Err(BufferExhausted);
        }
        self.offset = bit;
        Ok(())
    }

    /// Advance the cursor by the given number of bits.
    pub fn skip(&mut self, bits: usize) -> Result<(), BufferExhausted> {
        if bits > self.bits_rem() {
            return Err(BufferExhausted);
        }
        self.offset += bits;
        Ok(())
    }

    /// Create borrowed copy of the current cursor.
    ///
    /// Mutations on this copy affects the same buffer, but not the offset offset of the original
    /// owner. This is useful for reverting a sequence of writes if any of them fail.
    ///
    /// ```
    /// use bit_mangle::MutCursor;
    /// let mut buf = [0; 1];
    /// let mut cursor = MutCursor::from_slice(&mut buf);
    ///
    /// let mut borrowed = cursor.checkpoint();
    /// borrowed.encode_u4(0b1001).unwrap();
    ///
    /// assert_eq!(borrowed.bit_offset(), 4);
    /// assert_eq!(cursor.bit_offset(), 0);
    ///
    /// // Note that the data is still written to the butter
    /// assert_eq!(buf, [0b1001_0000]);
    ///
    /// // To commit the write, use seek
    /// // let offset = borrowed.offset();
    /// // cursor.seek(offset).unwrap();
    /// ```
    pub fn checkpoint(&mut self) -> MutCursor<'_> {
        MutCursor {
            buf: self.buf,
            offset: self.offset,
        }
    }

    fn encode_var_u8(&mut self, bits: usize, mut value: u8) -> Result<(), BufferExhausted> {
        if bits > 8 {
            panic!(
                "Encode called with invalid bit width {} (expected 0-8)",
                bits
            );
        }
        if self.bits_rem() < bits {
            return Err(BufferExhausted);
        }

        // Split the write across byte boundaries until all bits are consumed
        let mut rem_bits = bits;
        while rem_bits > 0 {
            let byte_offset = self.byte_offset();
            let bit_offset = self.offset % 8;

            // Figure out how many bits we can write before hitting a byte boundary
            let consumed_bits = (8 - bit_offset).min(rem_bits);
            rem_bits -= consumed_bits;

            // Extract the top bits so we can write them and then mask them off for the next
            // iteration
            let rem_mask = 0xffu8.checked_shr(8 - rem_bits as u32).unwrap_or(0);
            let curr_value = (value & !rem_mask) >> rem_bits;
            value &= rem_mask;

            // Zero the memory where we write the current bits
            let cleared_value =
                !(0xff << (8 - consumed_bits) >> bit_offset) & self.buf[byte_offset];

            // Write the current bits
            self.buf[byte_offset] =
                cleared_value | curr_value << (8 - bit_offset - consumed_bits) & 0xff >> bit_offset;

            self.offset += consumed_bits;
        }
        Ok(())
    }

    fn encode_var_u16(&mut self, bits: usize, value: u16) -> Result<(), BufferExhausted> {
        if bits > 16 {
            panic!(
                "Encode called with invalid bit width {} (expected 8-16)",
                bits
            );
        }
        if self.bits_rem() < bits {
            return Err(BufferExhausted);
        }
        let bytes = value.to_be_bytes();
        self.encode_var_u8(bits.saturating_sub(8), bytes[0])?;
        self.encode_var_u8(bits.min(8), bytes[1])?;
        Ok(())
    }

    fn encode_var_u32(&mut self, bits: usize, value: u32) -> Result<(), BufferExhausted> {
        if bits > 32 {
            panic!(
                "Encode called with invalid bit width {} (expected 0-32)",
                bits
            );
        }
        if self.bits_rem() < bits {
            return Err(BufferExhausted);
        }
        let bytes = value.to_be_bytes();
        self.encode_var_u16(
            bits.saturating_sub(16),
            u16::from_be_bytes([bytes[0], bytes[1]]),
        )?;
        self.encode_var_u16(bits.min(16), u16::from_be_bytes([bytes[2], bytes[3]]))?;
        Ok(())
    }

    /// Encode a boolean value as a single bit and advance the cursor.
    pub fn encode_bool(&mut self, value: bool) -> Result<(), BufferExhausted> {
        self.encode_u1(u8::from(value))
    }
}

macro_rules! impl_encode_u {
    ($method:ident, $bits:literal, $value_type:ty, $internal_encoder:ident) => {
        /// Encode the given number of bits and advance the cursor.
        ///
        /// Network byte order (big endian) is assumed.
        ///
        /// This will silently truncate bits outside above the given bit range.
        impl<'a> MutCursor<'a> {
            pub fn $method(&mut self, value: $value_type) -> Result<(), BufferExhausted> {
                self.$internal_encoder($bits, value)
            }
        }
    };
}

macro_rules! impl_encode_i {
    ($method:ident, $bits:literal, $value_type_i:ty, $value_type_u:ty, $internal_encoder:ident) => {
        impl<'a> MutCursor<'a> {
            /// Encode the given number of bits and advance the cursor.
            ///
            /// Twos complement and network byte order (big endian) is assumed.
            ///
            /// This will silently truncate bits outside above the given bit range.
            pub fn $method(&mut self, value: $value_type_i) -> Result<(), BufferExhausted> {
                self.$internal_encoder($bits, value as $value_type_u)
            }
        }
    };
}

impl_encode_u!(encode_u1, 1, u8, encode_var_u8);
impl_encode_u!(encode_u2, 2, u8, encode_var_u8);
impl_encode_u!(encode_u3, 3, u8, encode_var_u8);
impl_encode_u!(encode_u4, 4, u8, encode_var_u8);
impl_encode_u!(encode_u5, 5, u8, encode_var_u8);
impl_encode_u!(encode_u6, 6, u8, encode_var_u8);
impl_encode_u!(encode_u7, 7, u8, encode_var_u8);
impl_encode_u!(encode_u8, 8, u8, encode_var_u8);

impl_encode_u!(encode_u9, 9, u16, encode_var_u16);
impl_encode_u!(encode_u10, 10, u16, encode_var_u16);
impl_encode_u!(encode_u11, 11, u16, encode_var_u16);
impl_encode_u!(encode_u12, 12, u16, encode_var_u16);
impl_encode_u!(encode_u13, 13, u16, encode_var_u16);
impl_encode_u!(encode_u14, 14, u16, encode_var_u16);
impl_encode_u!(encode_u15, 15, u16, encode_var_u16);
impl_encode_u!(encode_u16, 16, u16, encode_var_u16);

impl_encode_u!(encode_u17, 17, u32, encode_var_u32);
impl_encode_u!(encode_u18, 18, u32, encode_var_u32);
impl_encode_u!(encode_u19, 19, u32, encode_var_u32);
impl_encode_u!(encode_u20, 20, u32, encode_var_u32);
impl_encode_u!(encode_u21, 21, u32, encode_var_u32);
impl_encode_u!(encode_u22, 22, u32, encode_var_u32);
impl_encode_u!(encode_u23, 23, u32, encode_var_u32);
impl_encode_u!(encode_u24, 24, u32, encode_var_u32);
impl_encode_u!(encode_u25, 25, u32, encode_var_u32);
impl_encode_u!(encode_u26, 26, u32, encode_var_u32);
impl_encode_u!(encode_u27, 27, u32, encode_var_u32);
impl_encode_u!(encode_u28, 28, u32, encode_var_u32);
impl_encode_u!(encode_u29, 29, u32, encode_var_u32);
impl_encode_u!(encode_u30, 30, u32, encode_var_u32);
impl_encode_u!(encode_u31, 31, u32, encode_var_u32);
impl_encode_u!(encode_u32, 32, u32, encode_var_u32);

impl_encode_i!(encode_i1, 1, i8, u8, encode_var_u8);
impl_encode_i!(encode_i2, 2, i8, u8, encode_var_u8);
impl_encode_i!(encode_i3, 3, i8, u8, encode_var_u8);
impl_encode_i!(encode_i4, 4, i8, u8, encode_var_u8);
impl_encode_i!(encode_i5, 5, i8, u8, encode_var_u8);
impl_encode_i!(encode_i6, 6, i8, u8, encode_var_u8);
impl_encode_i!(encode_i7, 7, i8, u8, encode_var_u8);
impl_encode_i!(encode_i8, 8, i8, u8, encode_var_u8);

impl_encode_i!(encode_i9, 9, i16, u16, encode_var_u16);
impl_encode_i!(encode_i10, 10, i16, u16, encode_var_u16);
impl_encode_i!(encode_i11, 11, i16, u16, encode_var_u16);
impl_encode_i!(encode_i12, 12, i16, u16, encode_var_u16);
impl_encode_i!(encode_i13, 13, i16, u16, encode_var_u16);
impl_encode_i!(encode_i14, 14, i16, u16, encode_var_u16);
impl_encode_i!(encode_i15, 15, i16, u16, encode_var_u16);
impl_encode_i!(encode_i16, 16, i16, u16, encode_var_u16);

impl_encode_i!(encode_i17, 17, i32, u32, encode_var_u32);
impl_encode_i!(encode_i18, 18, i32, u32, encode_var_u32);
impl_encode_i!(encode_i19, 19, i32, u32, encode_var_u32);
impl_encode_i!(encode_i20, 20, i32, u32, encode_var_u32);
impl_encode_i!(encode_i21, 21, i32, u32, encode_var_u32);
impl_encode_i!(encode_i22, 22, i32, u32, encode_var_u32);
impl_encode_i!(encode_i23, 23, i32, u32, encode_var_u32);
impl_encode_i!(encode_i24, 24, i32, u32, encode_var_u32);
impl_encode_i!(encode_i25, 25, i32, u32, encode_var_u32);
impl_encode_i!(encode_i26, 26, i32, u32, encode_var_u32);
impl_encode_i!(encode_i27, 27, i32, u32, encode_var_u32);
impl_encode_i!(encode_i28, 28, i32, u32, encode_var_u32);
impl_encode_i!(encode_i29, 29, i32, u32, encode_var_u32);
impl_encode_i!(encode_i30, 30, i32, u32, encode_var_u32);
impl_encode_i!(encode_i31, 31, i32, u32, encode_var_u32);
impl_encode_i!(encode_i32, 32, i32, u32, encode_var_u32);

impl<'a> MutCursor<'a> {
    pub fn commit(&mut self, other: &Self) {
        self.offset = other.offset;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test_encode_u {
        ($test:ident, $method:ident, $bits:literal, $value_type:ty, $value:literal) => {
            #[test]
            fn $test() {
                let value: $value_type = $value;
                let bits: usize = $bits;
                let expected: u32 = (value as u32) << (32 - bits);

                for skip in 0..32 - bits {
                    let mut buf = [0u8; 4];
                    let mut cursor = MutCursor::from_slice(&mut buf);
                    cursor.skip(skip).unwrap();
                    cursor.$method(value).unwrap();
                    let result = u32::from_be_bytes(buf);
                    assert_eq!(
                        result,
                        expected >> skip,
                        "{:032b} != {:032b}",
                        result,
                        expected >> skip
                    );
                }
            }
        };
    }

    macro_rules! test_encode_i {
        ($test:ident, $method:ident, $bits:literal, $value_type:ty) => {
            #[test]
            fn $test() {
                let bits: usize = $bits;
                for skip in 0..32 - bits {
                    let mut buf = [0u8; 4];
                    let mut cursor = MutCursor::from_slice(&mut buf);
                    cursor.skip(skip).unwrap();
                    cursor.$method(-1).unwrap();
                    let result = u32::from_be_bytes(buf);

                    let expected = (u32::MAX << (32 - bits)) >> skip;
                    assert_eq!(result, expected, "{:032b} != {:032b}", result, expected);
                }
            }
        };
    }

    test_encode_u!(test_encode_u1, encode_u1, 1, u8, 1);
    test_encode_u!(test_encode_u2, encode_u2, 2, u8, 0b11);
    test_encode_u!(test_encode_u3, encode_u3, 3, u8, 0b101);
    test_encode_u!(test_encode_u4, encode_u4, 4, u8, 0b1001);
    test_encode_u!(test_encode_u5, encode_u5, 5, u8, 0b1_0001);
    test_encode_u!(test_encode_u6, encode_u6, 6, u8, 0b10_0001);
    test_encode_u!(test_encode_u7, encode_u7, 7, u8, 0b100_0001);
    test_encode_u!(test_encode_u8, encode_u8, 8, u8, 0b1000_0001);

    test_encode_u!(test_encode_u9, encode_u9, 9, u16, 0b1_0000_0001);
    test_encode_u!(test_encode_u10, encode_u10, 10, u16, 0b10_0000_0001);
    test_encode_u!(test_encode_u11, encode_u11, 11, u16, 0b100_0000_0001);
    test_encode_u!(test_encode_u12, encode_u12, 12, u16, 0b1000_0000_0001);
    test_encode_u!(test_encode_u13, encode_u13, 13, u16, 0b1_0000_0000_0001);
    test_encode_u!(test_encode_u14, encode_u14, 14, u16, 0b10_0000_0000_0001);
    test_encode_u!(test_encode_u15, encode_u15, 15, u16, 0b100_0000_0000_0001);
    test_encode_u!(test_encode_u16, encode_u16, 16, u16, 0b1000_0000_0000_0001);

    test_encode_u!(
        test_encode_u17,
        encode_u17,
        17,
        u32,
        0b1_0000_0000_0000_0001
    );
    test_encode_u!(
        test_encode_u18,
        encode_u18,
        18,
        u32,
        0b10_0000_0000_0000_0001
    );
    test_encode_u!(
        test_encode_u19,
        encode_u19,
        19,
        u32,
        0b100_0000_0000_0000_0001
    );
    test_encode_u!(
        test_encode_u20,
        encode_u20,
        20,
        u32,
        0b1000_0000_0000_0000_0001
    );
    test_encode_u!(
        test_encode_u21,
        encode_u21,
        21,
        u32,
        0b1_0000_0000_0000_0000_0001
    );
    test_encode_u!(
        test_encode_u22,
        encode_u22,
        22,
        u32,
        0b10_0000_0000_0000_0000_0001
    );
    test_encode_u!(
        test_encode_u23,
        encode_u23,
        23,
        u32,
        0b100_0000_0000_0000_0000_0001
    );
    test_encode_u!(
        test_encode_u24,
        encode_u24,
        24,
        u32,
        0b1000_0000_0000_0000_0000_0001
    );
    test_encode_u!(
        test_encode_u25,
        encode_u25,
        25,
        u32,
        0b1_0000_0000_0000_0000_0000_0001
    );
    test_encode_u!(
        test_encode_u26,
        encode_u26,
        26,
        u32,
        0b10_0000_0000_0000_0000_0000_0001
    );
    test_encode_u!(
        test_encode_u27,
        encode_u27,
        27,
        u32,
        0b100_0000_0000_0000_0000_0000_0001
    );
    test_encode_u!(
        test_encode_u28,
        encode_u28,
        28,
        u32,
        0b1000_0000_0000_0000_0000_0000_0001
    );
    test_encode_u!(
        test_encode_u29,
        encode_u29,
        29,
        u32,
        0b1_0000_0000_0000_0000_0000_0000_0001
    );
    test_encode_u!(
        test_encode_u30,
        encode_u30,
        30,
        u32,
        0b10_0000_0000_0000_0000_0000_0000_0001
    );
    test_encode_u!(
        test_encode_u31,
        encode_u31,
        31,
        u32,
        0b100_0000_0000_0000_0000_0000_0000_0001
    );
    test_encode_u!(
        test_encode_u32,
        encode_u32,
        32,
        u32,
        0b1000_0000_0000_0000_0000_0000_0000_0001
    );

    test_encode_i!(test_encode_i1, encode_i1, 1, i8);
    test_encode_i!(test_encode_i2, encode_i2, 2, i8);
    test_encode_i!(test_encode_i3, encode_i3, 3, i8);
    test_encode_i!(test_encode_i4, encode_i4, 4, i8);
    test_encode_i!(test_encode_i5, encode_i5, 5, i8);
    test_encode_i!(test_encode_i6, encode_i6, 6, i8);
    test_encode_i!(test_encode_i7, encode_i7, 7, i8);
    test_encode_i!(test_encode_i8, encode_i8, 8, i8);

    test_encode_i!(test_encode_i9, encode_i9, 9, i16);
    test_encode_i!(test_encode_i10, encode_i10, 10, i16);
    test_encode_i!(test_encode_i11, encode_i11, 11, i16);
    test_encode_i!(test_encode_i12, encode_i12, 12, i16);
    test_encode_i!(test_encode_i13, encode_i13, 13, i16);
    test_encode_i!(test_encode_i14, encode_i14, 14, i16);
    test_encode_i!(test_encode_i15, encode_i15, 15, i16);
    test_encode_i!(test_encode_i16, encode_i16, 16, i16);

    test_encode_i!(test_encode_i17, encode_i17, 17, i32);
    test_encode_i!(test_encode_i18, encode_i18, 18, i32);
    test_encode_i!(test_encode_i19, encode_i19, 19, i32);
    test_encode_i!(test_encode_i20, encode_i20, 20, i32);
    test_encode_i!(test_encode_i21, encode_i21, 21, i32);
    test_encode_i!(test_encode_i22, encode_i22, 22, i32);
    test_encode_i!(test_encode_i23, encode_i23, 23, i32);
    test_encode_i!(test_encode_i24, encode_i24, 24, i32);
    test_encode_i!(test_encode_i25, encode_i25, 25, i32);
    test_encode_i!(test_encode_i26, encode_i26, 26, i32);
    test_encode_i!(test_encode_i27, encode_i27, 27, i32);
    test_encode_i!(test_encode_i28, encode_i28, 28, i32);
    test_encode_i!(test_encode_i29, encode_i29, 29, i32);
    test_encode_i!(test_encode_i30, encode_i30, 30, i32);
    test_encode_i!(test_encode_i31, encode_i31, 31, i32);
    test_encode_i!(test_encode_i32, encode_i32, 32, i32);

    #[test]
    fn test_overwrite_ones() {
        // Ensure that we don't rely on the buffer being zeroed before writing
        let mut buf = [0xff; 2];
        let mut cursor = MutCursor::from_slice(&mut buf);
        cursor.skip(1).unwrap();
        cursor.encode_u14(0).unwrap();
        assert_eq!(buf, [0b1000_0000, 0b0000_0001]);
    }

    #[test]
    fn test_checkpoint_with_revert() {
        let mut buf = [0; 1];
        let mut cursor = MutCursor::from_slice(&mut buf);
        cursor.skip(1).unwrap();

        let mut checkpoint = cursor.checkpoint();
        checkpoint.encode_bool(true).unwrap();

        cursor.encode_bool(true).unwrap();
        assert_eq!(buf, [0b0100_0000]);
    }

    #[test]
    fn test_checkpoint_with_commit() {
        let mut buf = [0; 1];
        let mut cursor = MutCursor::from_slice(&mut buf);
        cursor.skip(1).unwrap();

        let mut checkpoint = cursor.checkpoint();
        checkpoint.encode_bool(true).unwrap();
        let offset = checkpoint.bit_offset();
        cursor.seek(offset).unwrap();

        cursor.encode_bool(true).unwrap();
        assert_eq!(buf, [0b0110_0000]);
    }

    #[test]
    fn test_seek() {
        let mut buf = [0u8];
        let mut cursor = MutCursor::from_slice(&mut buf);

        assert_eq!(cursor.seek(1), Ok(()));
        assert_eq!(cursor.bits_rem(), 7);

        // This previously triggered a bug due to an invalid bounds check
        assert_eq!(cursor.seek(7), Ok(()));
        assert_eq!(cursor.seek(6), Ok(()));

        assert_eq!(cursor.seek(8), Err(BufferExhausted));
    }
}
