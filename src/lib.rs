#![doc = include_str!("../README.MD")]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "nightly", feature(allocator_api))]
extern crate alloc;

pub mod raw_alloc;
pub use raw_alloc::*;
pub mod allocator_api;
pub use allocator_api::*;
