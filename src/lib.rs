#![no_std]

mod cursor;
mod mut_cursor;

pub use cursor::*;
pub use mut_cursor::*;

#[derive(Debug, PartialEq, Eq)]
pub struct BufferExhausted;
