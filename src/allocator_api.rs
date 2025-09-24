//! Bindings for allocator_api that allow usage within both nightly and stable.

// Import and re-export allocator types from internal prelude
pub use crate::prelude::{Allocator, Layout, AllocError, Global};
