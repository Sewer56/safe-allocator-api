//! A safe wrapper around low-level allocation primitives from `alloc::alloc`.
//!
//! This crate provides a safe interface for working with raw allocations while maintaining
//! the same error handling semantics as the underlying allocation APIs.
use core::ptr::NonNull;
use core::{alloc::Layout, fmt};

use allocator_api2::alloc::{AllocError, Allocator, Global};

/// A safe wrapper around a raw allocation with known layout.
///
/// # Safety
///
/// This type ensures that:
/// - The wrapped pointer is always non-null and properly aligned
/// - Memory is automatically deallocated when dropped
/// - Reallocation maintains proper alignment and size constraints
///
/// # Example
///
/// ```rust
/// # use core::alloc::Layout;
/// use safe_allocator_api::RawAlloc;
///
/// // Create a new allocation of 1024 bytes
/// let layout = Layout::array::<u8>(1024).unwrap();
/// let mut alloc = RawAlloc::new(layout).expect("allocation failed");
///
/// // Write some data
/// unsafe {
///     core::ptr::write(alloc.as_mut_ptr(), 42u8);
/// }
///
/// // Automatically deallocated when dropped
/// ```
pub struct RawAlloc<A: Allocator = Global> {
    ptr: NonNull<[u8]>,
    layout: Layout,
    allocator: A,
}

impl<A: Allocator> RawAlloc<A> {
    /// Creates a new allocation with the given layout using the provided allocator.
    ///
    /// This is equivalent to calling [`Allocator::allocate`] but provides automatic
    /// cleanup when the allocation is no longer needed.
    ///
    /// # Arguments
    ///
    /// * `layout` - The desired memory layout
    /// * `allocator` - The allocator to use
    ///
    /// # Errors
    ///
    /// Returns [`AllocError`] if the allocator reports an error or if the layout
    /// has a size of 0.
    ///
    /// # Example
    ///
    /// ```rust
    /// #![feature(allocator_api)]
    ///
    /// use core::alloc::Layout;
    /// use allocator_api2::alloc::*;
    /// use safe_allocator_api::RawAlloc;
    ///
    /// let layout = Layout::new::<u64>();
    /// let alloc = RawAlloc::new_in(layout, Global)?;
    /// # Ok::<_, AllocError>(())
    /// ```
    pub fn new_in(layout: Layout, allocator: A) -> Result<Self, AllocError> {
        if layout.size() == 0 {
            return Err(AllocError);
        }

        let ptr = allocator.allocate(layout)?;

        Ok(Self {
            ptr,
            layout,
            allocator,
        })
    }

    /// Creates a new zeroed allocation with the given layout using the provided allocator.
    ///
    /// This is equivalent to calling [`Allocator::allocate_zeroed`] but provides automatic
    /// cleanup when the allocation is no longer needed.
    ///
    /// # Errors
    ///
    /// Returns [`AllocError`] if the allocator reports an error or if the layout
    /// has a size of 0.
    pub fn new_zeroed_in(layout: Layout, allocator: A) -> Result<Self, AllocError> {
        if layout.size() == 0 {
            return Err(AllocError);
        }

        let ptr = allocator.allocate_zeroed(layout)?;

        Ok(Self {
            ptr,
            layout,
            allocator,
        })
    }

    /// Attempts to grow the allocation to the new layout.
    ///
    /// # Errors
    ///
    /// Returns [`AllocError`] if:
    /// - The allocator reports an error
    /// - The new layout has a size of 0
    /// - The new size is smaller than the current size (use [`Self::shrink`] instead)
    ///
    /// # Example
    ///
    /// ```rust
    /// use allocator_api2::alloc::*;
    /// use safe_allocator_api::RawAlloc;
    ///
    /// let layout = Layout::array::<u8>(100).unwrap();
    /// let mut alloc = RawAlloc::new(layout)?;
    ///
    /// // Grow the allocation
    /// let new_layout = Layout::array::<u8>(200).unwrap();
    /// alloc.grow(new_layout)?;
    /// # Ok::<_, AllocError>(())
    /// ```
    pub fn grow(&mut self, new_layout: Layout) -> Result<(), AllocError> {
        if new_layout.size() == 0 {
            return Err(AllocError);
        }
        if new_layout.size() <= self.layout.size() {
            return Err(AllocError);
        }

        let new_ptr = unsafe {
            self.allocator.grow(
                NonNull::new_unchecked(self.ptr.as_ptr() as *mut u8),
                self.layout,
                new_layout,
            )?
        };

        self.ptr = new_ptr;
        self.layout = new_layout;
        Ok(())
    }

    /// Attempts to grow the allocation to the new layout, zeroing the additional memory.
    ///
    /// This is equivalent to [`Self::grow`] but ensures any additional memory is zeroed.
    ///
    /// # Errors
    ///
    /// Returns [`AllocError`] if:
    /// - The allocator reports an error
    /// - The new layout has a size of 0
    /// - The new size is smaller than the current size (use [`Self::shrink`] instead)
    pub fn grow_zeroed(&mut self, new_layout: Layout) -> Result<(), AllocError> {
        if new_layout.size() == 0 {
            return Err(AllocError);
        }
        if new_layout.size() <= self.layout.size() {
            return Err(AllocError);
        }

        let new_ptr = unsafe {
            self.allocator.grow_zeroed(
                NonNull::new_unchecked(self.ptr.as_ptr() as *mut u8),
                self.layout,
                new_layout,
            )?
        };

        self.ptr = new_ptr;
        self.layout = new_layout;
        Ok(())
    }

    /// Attempts to shrink the allocation to the new layout.
    ///
    /// # Errors
    ///
    /// Returns [`AllocError`] if:
    /// - The allocator reports an error
    /// - The new layout has a size of 0
    /// - The new size is larger than the current size (use [`Self::grow`] instead)
    ///
    /// # Example
    ///
    /// ```rust
    /// use allocator_api2::alloc::*;
    /// use safe_allocator_api::RawAlloc;
    ///
    /// let layout = Layout::array::<u8>(200).unwrap();
    /// let mut alloc = RawAlloc::new(layout)?;
    ///
    /// // Shrink the allocation
    /// let new_layout = Layout::array::<u8>(100).unwrap();
    /// alloc.shrink(new_layout)?;
    /// # Ok::<_, AllocError>(())
    /// ```
    pub fn shrink(&mut self, new_layout: Layout) -> Result<(), AllocError> {
        if new_layout.size() == 0 {
            return Err(AllocError);
        }
        if new_layout.size() >= self.layout.size() {
            return Err(AllocError);
        }

        let new_ptr = unsafe {
            self.allocator.shrink(
                NonNull::new_unchecked(self.ptr.as_ptr() as *mut u8),
                self.layout,
                new_layout,
            )?
        };

        self.ptr = new_ptr;
        self.layout = new_layout;
        Ok(())
    }

    /// Returns a raw pointer to the allocated memory.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the memory is accessed according to
    /// the original layout constraints.
    pub fn as_ptr(&self) -> *const u8 {
        self.ptr.as_ptr() as *const u8
    }

    /// Returns a raw mutable pointer to the allocated memory.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the memory is accessed according to
    /// the original layout constraints.
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.ptr.as_ptr() as *mut u8
    }

    /// Returns the layout used for this allocation.
    pub fn layout(&self) -> Layout {
        self.layout
    }
}

impl<A: Allocator> Drop for RawAlloc<A> {
    fn drop(&mut self) {
        unsafe {
            self.allocator.deallocate(
                NonNull::new_unchecked(self.ptr.as_ptr() as *mut u8),
                self.layout,
            );
        }
    }
}

impl<A: Allocator> fmt::Debug for RawAlloc<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RawAlloc")
            .field("ptr", &self.ptr)
            .field("layout", &self.layout)
            .finish()
    }
}

// Convenience constructors using the Global allocator
impl RawAlloc {
    /// Creates a new allocation with the given layout using the global allocator.
    ///
    /// This is equivalent to calling [`Self::new_in`] with the global allocator.
    pub fn new(layout: Layout) -> Result<Self, AllocError> {
        Self::new_in(layout, Global)
    }

    /// Creates a new zeroed allocation with the given layout using the global allocator.
    ///
    /// This is equivalent to calling [`Self::new_zeroed_in`] with the global allocator.
    pub fn new_zeroed(layout: Layout) -> Result<Self, AllocError> {
        Self::new_zeroed_in(layout, Global)
    }
}

// Cannot implement Send + Sync automatically due to the raw pointer
// Users must opt-in by implementing these traits based on their usage
unsafe impl<A: Allocator> Send for RawAlloc<A> {}
unsafe impl<A: Allocator> Sync for RawAlloc<A> {}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::size_of;

    #[test]
    fn zero_sized_alloc_returns_error() {
        let layout = Layout::from_size_align(0, 1).unwrap();
        assert!(RawAlloc::new(layout).is_err());
    }

    #[test]
    fn basic_alloc_and_write() {
        let layout = Layout::new::<u32>();
        let mut alloc = RawAlloc::new(layout).unwrap();

        unsafe {
            core::ptr::write(alloc.as_mut_ptr() as *mut u32, 0xDEADBEEF);
            assert_eq!(core::ptr::read(alloc.as_ptr() as *const u32), 0xDEADBEEF);
        }
    }

    #[test]
    fn zeroed_allocation() {
        let size = 1024;
        let layout = Layout::array::<u8>(size).unwrap();
        let alloc = RawAlloc::new_zeroed(layout).unwrap();

        unsafe {
            let slice = core::slice::from_raw_parts(alloc.as_ptr(), size);
            assert!(slice.iter().all(|&x| x == 0));
        }
    }

    #[test]
    fn custom_allocator() {
        let layout = Layout::new::<i32>();
        let alloc = RawAlloc::new_in(layout, Global).unwrap();
        assert_eq!(alloc.layout().size(), size_of::<i32>());
    }

    #[test]
    fn array_allocation() {
        let elements = 100;
        let layout = Layout::array::<u64>(elements).unwrap();
        let mut alloc = RawAlloc::new(layout).unwrap();

        unsafe {
            let slice = core::slice::from_raw_parts_mut(alloc.as_mut_ptr() as *mut u64, elements);

            for (i, item) in slice.iter_mut().enumerate() {
                *item = i as u64;
            }

            assert_eq!(slice[42], 42);
        }
    }

    #[test]
    fn alignment_requirements() {
        let align = 64; // Test a large alignment
        let size = 128;
        let layout = Layout::from_size_align(size, align).unwrap();
        let alloc = RawAlloc::new(layout).unwrap();

        let addr = alloc.as_ptr() as usize;
        assert_eq!(addr % align, 0, "Allocation not properly aligned");
    }

    #[test]
    fn multiple_allocations() {
        let layout = Layout::new::<u8>();
        let mut allocations = Vec::new();

        // Create many allocations to stress the allocator
        for i in 0..100 {
            let mut alloc = RawAlloc::new(layout).unwrap();
            unsafe {
                core::ptr::write(alloc.as_mut_ptr(), i as u8);
            }
            allocations.push(alloc);
        }

        // Verify each allocation is independent
        for (i, alloc) in allocations.iter().enumerate() {
            unsafe {
                assert_eq!(core::ptr::read(alloc.as_ptr()), i as u8);
            }
        }
    }

    #[test]
    fn oversized_allocation() {
        // Try to allocate a very large size (but not so large it would definitely fail)
        let layout = Layout::array::<u8>(1024 * 1024).unwrap();
        let result = RawAlloc::new(layout);

        // We don't assert success or failure here, as it depends on the system,
        // but we verify it doesn't panic
        let _ = result.is_ok();
    }

    #[test]
    fn grow_allocation() {
        let initial_size = 100;
        let layout = Layout::array::<u8>(initial_size).unwrap();
        let mut alloc = RawAlloc::new(layout).unwrap();

        // Write some data
        unsafe {
            let slice = core::slice::from_raw_parts_mut(alloc.as_mut_ptr(), initial_size);
            slice[0] = 42;
        }

        // Grow the allocation
        let new_size = 200;
        let new_layout = Layout::array::<u8>(new_size).unwrap();
        alloc.grow(new_layout).unwrap();

        // Verify the data is preserved
        unsafe {
            let slice = core::slice::from_raw_parts(alloc.as_ptr(), new_size);
            assert_eq!(slice[0], 42);
        }
    }

    #[test]
    fn grow_zeroed_allocation() {
        let initial_size = 100;
        let layout = Layout::array::<u8>(initial_size).unwrap();
        let mut alloc = RawAlloc::new(layout).unwrap();

        // Write some data
        unsafe {
            let slice = core::slice::from_raw_parts_mut(alloc.as_mut_ptr(), initial_size);
            slice[0] = 42;
        }

        // Grow the allocation
        let new_size = 200;
        let new_layout = Layout::array::<u8>(new_size).unwrap();
        alloc.grow_zeroed(new_layout).unwrap();

        unsafe {
            let slice = core::slice::from_raw_parts(alloc.as_ptr(), new_size);
            // Verify original data is preserved
            assert_eq!(slice[0], 42);
            // Verify new memory is zeroed
            assert!(slice[initial_size..].iter().all(|&x| x == 0));
        }
    }

    #[test]
    fn shrink_allocation() {
        let initial_size = 200;
        let layout = Layout::array::<u8>(initial_size).unwrap();
        let mut alloc = RawAlloc::new(layout).unwrap();

        // Write some data
        unsafe {
            let slice = core::slice::from_raw_parts_mut(alloc.as_mut_ptr(), initial_size);
            slice[0] = 42;
        }

        // Shrink the allocation
        let new_size = 100;
        let new_layout = Layout::array::<u8>(new_size).unwrap();
        alloc.shrink(new_layout).unwrap();

        // Verify the data is preserved
        unsafe {
            let slice = core::slice::from_raw_parts(alloc.as_ptr(), new_size);
            assert_eq!(slice[0], 42);
        }
    }

    #[test]
    fn grow_zero_size_fails() {
        let layout = Layout::array::<u8>(100).unwrap();
        let mut alloc = RawAlloc::new(layout).unwrap();

        let new_layout = Layout::from_size_align(0, 1).unwrap();
        assert!(alloc.grow(new_layout).is_err());
    }

    #[test]
    fn shrink_zero_size_fails() {
        let layout = Layout::array::<u8>(100).unwrap();
        let mut alloc = RawAlloc::new(layout).unwrap();

        let new_layout = Layout::from_size_align(0, 1).unwrap();
        assert!(alloc.shrink(new_layout).is_err());
    }

    #[test]
    fn grow_smaller_size_fails() {
        let layout = Layout::array::<u8>(200).unwrap();
        let mut alloc = RawAlloc::new(layout).unwrap();

        let new_layout = Layout::array::<u8>(100).unwrap();
        assert!(alloc.grow(new_layout).is_err());
    }

    #[test]
    fn shrink_larger_size_fails() {
        let layout = Layout::array::<u8>(100).unwrap();
        let mut alloc = RawAlloc::new(layout).unwrap();

        let new_layout = Layout::array::<u8>(200).unwrap();
        assert!(alloc.shrink(new_layout).is_err());
    }
}
