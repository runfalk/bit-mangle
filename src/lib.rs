#![cfg_attr(not(feature = "std"), no_std)]

mod cursor;
mod mut_cursor;

pub use cursor::*;
pub use mut_cursor::*;

#[derive(Debug, PartialEq, Eq)]
pub struct BufferExhausted;

impl core::fmt::Display for BufferExhausted {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "buffer exhausted")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for BufferExhausted {}
