#![doc = include_str!("../README.MD")]
#![no_std]
#![cfg_attr(feature = "nightly", feature(allocator_api))]

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

pub mod raw_alloc;
pub use raw_alloc::*;
pub mod allocator_api;
pub use allocator_api::*;
