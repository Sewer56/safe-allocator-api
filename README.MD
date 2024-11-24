# safe-allocator-api

[![Crates.io](https://img.shields.io/crates/v/safe-allocator-api.svg)](https://crates.io/crates/safe-allocator-api)
[![Docs.rs](https://docs.rs/safe-allocator-api/badge.svg)](https://docs.rs/safe-allocator-api)
[![CI](https://github.com/Sewer56/safe-allocator-api/actions/workflows/rust.yml/badge.svg)](https://github.com/Sewer56/safe-allocator-api/actions)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A safe wrapper around the `allocator_api`'s [Allocator] trait.

This crate provides a wrapper around the returned results, ensuring that any allocated memory
is automatically dropped when its lifetime expires.

## Features

- Safe wrapper around raw allocations with known layout
- Automatic deallocation when values go out of scope
- Support for custom allocators
- Zero-initialization options
- Grow and shrink operations with proper error handling
- Thread-safe (implements `Send` and `Sync`)
  - Actual thread safety depends on safety of the allocator used internally, tread wisely.

In my case I wrote this crate to have a 'safe' way to make aligned allocations 😉.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
safe-allocator-api = "0.1.0"
```

## Examples

### Basic Allocation

```rust
#![feature(allocator_api)]
use core::alloc::*;
use safe_alloc::RawAlloc;

fn allocate_example() -> Result<(), AllocError> {
    // Create a new allocation of 1024 bytes
    let layout = Layout::array::<u8>(1024).unwrap();
    let mut alloc = RawAlloc::new(layout)?;
    
    // Write some data
    unsafe {
        core::ptr::write(alloc.as_mut_ptr(), 42u8);
    }
    
    // Memory is automatically deallocated when alloc goes out of scope
    Ok(())
}
```

### Zero-Initialized Memory

```rust
#![feature(allocator_api)]
use core::alloc::*;
use safe_alloc::RawAlloc;

fn zero_initialized_example() -> Result<(), AllocError> {
    // Create a zero-initialized allocation
    let layout = Layout::array::<u8>(1024).unwrap();
    let alloc = RawAlloc::new_zeroed(layout)?;
    
    // Verify memory is zeroed
    unsafe {
        let slice = core::slice::from_raw_parts(alloc.as_ptr(), 1024);
        assert!(slice.iter().all(|&x| x == 0));
    }
    
    Ok(())
}
```

### Growing and Shrinking Allocations

```rust
#![feature(allocator_api)]
use core::alloc::*;
use safe_alloc::RawAlloc;

fn grow_and_shrink_example() -> Result<(), AllocError> {
    // Start with a small allocation
    let layout = Layout::array::<u8>(100).unwrap();
    let mut alloc = RawAlloc::new(layout)?;
    
    // Grow the allocation
    let new_layout = Layout::array::<u8>(200).unwrap();
    alloc.grow(new_layout)?;
    
    // Shrink it back down
    let final_layout = Layout::array::<u8>(50).unwrap();
    alloc.shrink(final_layout)?;
    
    Ok(())
}
```

### Custom Allocators

```rust
#![feature(allocator_api)]
use core::alloc::*;
use std::alloc::Global;
use safe_alloc::RawAlloc;

fn custom_allocator_example() -> Result<(), AllocError> {
    let layout = Layout::new::<u64>();
    let alloc = RawAlloc::new_in(layout, Global)?;
    
    Ok(())
}
```

## Safety

This crate provides a safe interface by ensuring:
- The wrapped pointer is always non-null and properly aligned
- Memory is automatically deallocated when dropped
- Reallocation maintains proper alignment and size constraints
- Error conditions are properly handled and reported

## Error Handling

Operations will return `AllocError` in the following cases:
- The allocator reports an error
- Attempting to allocate zero bytes
- Growing to a smaller size
- Shrinking to a larger size

## Development

For information on how to work with this codebase, see [README-DEV.MD](README-DEV.MD).

## License

Licensed under [MIT](./LICENSE).  

[Learn more about Reloaded's general choice of licensing for projects.][reloaded-license].  

[codecov]: https://about.codecov.io/
[crates-io-key]: https://crates.io/settings/tokens
[nuget-key]: https://www.nuget.org/account/apikeys
[reloaded-license]: https://reloaded-project.github.io/Reloaded.MkDocsMaterial.Themes.R2/Pages/license/
[Allocator]: https://doc.rust-lang.org/std/alloc/trait.Allocator.html