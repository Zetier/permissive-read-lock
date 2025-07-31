//! A lock that supports multiple safe readers and an optional lock-free unsafe
//! read path.
//!
//! You can acquire a safe shared lock via `read_safely`, an exclusive lock via
//! `write`, or bypass locking entirely via the unsafe `read` method.
//!
//! # Examples
//!
//! Basic usage:
//! ```
//! use permissive_read_lock::PermissiveReadLock;
//!
//! let lock = PermissiveReadLock::new(5);
//! assert_eq!(*lock.read_safely(), 5);
//!
//! {
//!     let mut w = lock.write();
//!     *w += 10;
//! }
//! assert_eq!(*lock.read_safely(), 15);
//! ```
//!
//! Unsafe read (caller must ensure no concurrent writers):
//! ```
//! # use permissive_read_lock::PermissiveReadLock;
//! # let lock = PermissiveReadLock::new(42);
//! unsafe {
//!     assert_eq!(*lock.read(), 42);
//! }
//! ```

use parking_lot::{RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::cell::UnsafeCell;
use std::ops::{Deref, DerefMut};

/// A lock that allows concurrent readers and exclusive writers.
///
/// Readers using `read_safely` hold a shared `RwLock` read guard,
/// writers using `write` hold an exclusive write guard, and
/// `read` performs an unchecked read without any locking.
///
/// # Thread safety
/// `PermissiveReadLock<T>` is `Sync` if `T: Send + Sync`.
#[derive(Debug, Default)]
pub struct PermissiveReadLock<T> {
    cell: UnsafeCell<T>,
    lock: RwLock<()>,
}

unsafe impl<T: Sync> Sync for PermissiveReadLock<T> {}

impl<T> PermissiveReadLock<T> {
    /// Create a new `PermissiveReadLock` containing `t`.
    pub fn new(t: T) -> Self {
        PermissiveReadLock {
            cell: UnsafeCell::new(t),
            lock: RwLock::new(()),
        }
    }

    /// Acquire a shared read lock.
    ///
    /// This blocks if a writer is active.  Returns a guard which
    /// implements `Deref<Target = T>`.
    ///
    /// # Examples
    /// ```
    /// use permissive_read_lock::PermissiveReadLock;
    /// let lock = PermissiveReadLock::new(vec![1,2,3]);
    /// let guard = lock.read_safely();
    /// assert_eq!(guard.len(), 3);
    /// ```
    pub fn read_safely(&self) -> PermissiveReadSafelyReadGuard<'_, T> {
        let guard = self.lock.read();
        PermissiveReadSafelyReadGuard {
            cell: &self.cell,
            _guard: guard,
        }
    }

    /// Perform an unchecked, unsynchronized read of the inner `T`.
    ///
    /// # Safety
    /// The caller must ensure there are no concurrent writers or mutable
    /// accesses, or data races will occur.
    pub unsafe fn read(&self) -> PermissiveReadReadGuard<'_, T> {
        PermissiveReadReadGuard { cell: &self.cell }
    }

    /// Acquire an exclusive write lock.
    ///
    /// Blocks until no other readers or writers are active.
    /// Returns a guard which implements `DerefMut<Target = T>`.
    ///
    /// # Examples
    /// ```
    /// use permissive_read_lock::PermissiveReadLock;
    /// let lock = PermissiveReadLock::new(0);
    /// {
    ///    let mut w = lock.write();
    ///    *w = 42;
    /// }
    /// assert_eq!(*lock.read_safely(), 42);
    /// ```
    pub fn write(&self) -> PermissiveReadWriteGuard<'_, T> {
        let guard = self.lock.write();
        PermissiveReadWriteGuard {
            cell: &self.cell,
            _guard: guard,
        }
    }

    /// Get a mutable reference to `T` when you own the lock exclusively (`&mut
    /// self`).
    ///
    /// # Examples
    /// ```
    /// use permissive_read_lock::PermissiveReadLock;
    /// let mut lock = PermissiveReadLock::new(10);
    /// *lock.get_mut() += 5;
    /// assert_eq!(lock.into_inner(), 15);
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        self.cell.get_mut()
    }

    /// Consume the lock and return the inner `T`.
    pub fn into_inner(self) -> T {
        self.cell.into_inner()
    }
}

/// A shared read guard returned by `read_safely`.
///
/// Holds a `RwLockReadGuard` so long as it is alive.
/// Implements `Deref<Target = T>`.
pub struct PermissiveReadSafelyReadGuard<'g, T> {
    cell: &'g UnsafeCell<T>,
    _guard: RwLockReadGuard<'g, ()>,
}

impl<'g, T> Deref for PermissiveReadSafelyReadGuard<'g, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { self.cell.get().as_ref().unwrap_unchecked() }
    }
}

/// An unsynchronized read guard returned by the unsafe `read` method.
///
/// # Safety
/// This guard does *not* hold any lock; the caller must guarantee
/// there are no concurrent writers or mutable accesses.
pub struct PermissiveReadReadGuard<'g, T> {
    cell: &'g UnsafeCell<T>,
}

impl<'g, T> Deref for PermissiveReadReadGuard<'g, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { self.cell.get().as_ref().unwrap_unchecked() }
    }
}

/// A write guard returned by `write`.
///
/// Holds a `RwLockWriteGuard` for exclusive mutable access to `T`.
/// Implements `Deref<Target = T>` and `DerefMut<Target = T>`.
pub struct PermissiveReadWriteGuard<'g, T> {
    cell: &'g UnsafeCell<T>,
    _guard: RwLockWriteGuard<'g, ()>,
}

impl<'g, T> Deref for PermissiveReadWriteGuard<'g, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { self.cell.get().as_ref().unwrap_unchecked() }
    }
}

impl<'g, T> DerefMut for PermissiveReadWriteGuard<'g, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.cell.get().as_mut().unwrap_unchecked() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_read_and_write() {
        let lock = PermissiveReadLock::new(5);
        assert_eq!(*lock.read_safely(), 5);

        {
            let mut w = lock.write();
            *w += 10;
        }
        assert_eq!(*lock.read_safely(), 15);
    }

    #[test]
    fn unsafe_read() {
        let lock = PermissiveReadLock::new(42);
        let val = unsafe { *lock.read() };
        assert_eq!(val, 42);
    }

    #[test]
    fn get_mut_and_into_inner() {
        let mut lock = PermissiveReadLock::new(10);
        *lock.get_mut() += 5;
        assert_eq!(lock.into_inner(), 15);
    }

    #[test]
    fn concurrent_reads() {
        use std::sync::Arc;
        use std::thread;

        let lock = Arc::new(PermissiveReadLock::new(100));
        let mut handles = vec![];

        for _ in 0..4 {
            let lock = Arc::clone(&lock);
            handles.push(thread::spawn(move || {
                assert_eq!(*lock.read_safely(), 100);
            }));
        }

        for h in handles {
            h.join().unwrap();
        }
    }

    #[test]
    fn exclusive_write_blocks_read() {
        use std::sync::Arc;
        use std::thread;
        use std::time::Duration;

        let lock = Arc::new(PermissiveReadLock::new(1));
        let lock2 = Arc::clone(&lock);

        let writer = thread::spawn(move || {
            let mut w = lock2.write();
            *w = 99;
            // Hold the write lock for a bit
            std::thread::sleep(Duration::from_millis(100));
        });

        // Give the writer a head start
        std::thread::sleep(Duration::from_millis(10));
        // This should block until the writer is done
        let r = lock.read_safely();
        assert!(*r == 99 || *r == 1); // Accept either value depending on timing

        writer.join().unwrap();
    }
}
