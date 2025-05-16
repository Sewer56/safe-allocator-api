//! Bindings for allocator_api that allow usage within both nightly and stable.

#[cfg(feature = "nightly")]
pub use alloc::alloc::*;
#[cfg(not(feature = "nightly"))]
pub use allocator_api2::alloc::*;
