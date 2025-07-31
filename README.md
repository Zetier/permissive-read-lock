# permissive-read-lock

A lock that supports multiple safe readers and an optional lock-free unsafe read path.

## Overview

`PermissiveReadLock<T>` is a synchronization primitive that allows:

- Multiple safe, concurrent readers via `read_safely()`
- Exclusive writers via `write()`
- An *unsafe*, lock-free read path via `read()` (caller must guarantee no concurrent writers)

This is useful for scenarios where you want to allow fast, unsynchronized reads in performance-critical code, but still need safe access for most users.

## Examples

Basic usage:

```rust
use permissive_read_lock::PermissiveReadLock;

let lock = PermissiveReadLock::new(5);
assert_eq!(*lock.read_safely(), 5);

{
    let mut w = lock.write();
    *w += 10;
}
assert_eq!(*lock.read_safely(), 15);
```

Unsafe read (caller must ensure no concurrent writers):

```rust
use permissive_read_lock::PermissiveReadLock;
let lock = PermissiveReadLock::new(42);
unsafe {
    assert_eq!(*lock.read(), 42);
}
```

## Safety

- The `read()` method is unsafe: you must guarantee there are no concurrent writers or mutable accesses.
- The safe API (`read_safely`, `write`) uses a `RwLock` internally.

## License

MIT OR Apache-2.0
