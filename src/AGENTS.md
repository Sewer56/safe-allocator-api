# safe-allocator-api

A safe wrapper around the `allocator_api`'s Allocator trait, providing automatic deallocation and safe memory management.

# Project Structure

- `safe-allocator-api/` - Main library crate
  - `src/` - Library source code
    - `lib.rs` - Main library entry point
    - `prelude.rs` - Common imports
    - `raw_alloc.rs` - Core allocation wrapper

# Code Guidelines

- Optimize for performance; use zero-cost abstractions, avoid allocations.
- Keep modules under 500 lines (excluding tests); split if larger.
- Place `use` inside functions only for `#[cfg]` conditional compilation.
- Prefer `core` over `std` where possible (`core::mem` over `std::mem`).

# Documentation Standards

- Document public items with `///`
- Add examples in docs where helpful
- Use `//!` for module-level docs
- Focus comments on "why" not "what"
- Use [`TypeName`] rustdoc links, not backticks.

# Post-Change Verification

```bash
cargo test --workspace --all-features
cargo clippy --workspace --all-features -- -D warnings
cargo doc --workspace --all-features
cargo fmt --all
cargo publish --dry-run
```

All must pass before submitting.
