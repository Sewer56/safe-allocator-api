//! Prelude module for allocator API types.
//!
//! This module centralizes the conditional imports for allocator-related types,
//! allowing the rest of the crate to use consistent types regardless of whether
//! the nightly feature is enabled or not.

#[cfg(not(feature = "nightly"))]
pub use allocator_api2::alloc::Allocator;
#[cfg(feature = "nightly")]
pub use std::alloc::Allocator;

#[cfg(not(feature = "nightly"))]
pub use allocator_api2::alloc::Layout;
#[cfg(feature = "nightly")]
pub use core::alloc::Layout;

#[cfg(not(feature = "nightly"))]
pub use allocator_api2::alloc::AllocError;
#[cfg(feature = "nightly")]
pub use std::alloc::AllocError;

#[cfg(not(feature = "nightly"))]
pub use allocator_api2::alloc::Global;
#[cfg(feature = "nightly")]
pub use std::alloc::Global;
