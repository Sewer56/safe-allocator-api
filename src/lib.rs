#![doc = include_str!("../README.MD")]
#![cfg_attr(not(feature = "std"), no_std)]
extern crate alloc;

pub mod raw_alloc;
pub use raw_alloc::*;
