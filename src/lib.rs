#![doc = include_str!("../README.MD")]
#![no_std]
#![cfg_attr(feature = "nightly", feature(allocator_api))]

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

// Internal prelude module for conditional allocator imports
mod prelude;

pub mod raw_alloc;
pub use raw_alloc::*;
pub use prelude::*;
