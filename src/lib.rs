// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![no_std]

#![feature(const_align_of)]
#![feature(const_fn)]

use core::fmt;
use core::option::Option;
use core::marker::{PhantomData, Send, Sized, Sync};
use core::mem;

/// A wrapper around a raw non-null `*mut T` that indicates that the possessor
/// of this wrapper owns the referent. Useful for building abstractions like
/// `Box<T>`, `Vec<T>`, `String`, and `HashMap<K, V>`.
///
/// Unlike `*mut T`, `Unique<T>` behaves "as if" it were an instance of `T`.
/// It implements `Send`/`Sync` if `T` is `Send`/`Sync`. It also implies
/// the kind of strong aliasing guarantees an instance of `T` can expect:
/// the referent of the pointer should not be modified without a unique path to
/// its owning Unique.
///
/// If you're uncertain of whether it's correct to use `Unique` for your purposes,
/// consider using `Shared`, which has weaker semantics.
///
/// Unlike `*mut T`, the pointer must always be non-null, even if the pointer
/// is never dereferenced. This is so that enums may use this forbidden value
/// as a discriminant -- `Option<Unique<T>>` has the same size as `Unique<T>`.
/// However the pointer may still dangle if it isn't dereferenced.
///
/// Unlike `*mut T`, `Unique<T>` is covariant over `T`. This should always be correct
/// for any type which upholds Unique's aliasing requirements.
#[allow(missing_debug_implementations)]
pub struct Unique<T: ?Sized> {
    pointer: *const T,
    // NOTE: this marker has no consequences for variance, but is necessary
    // for dropck to understand that we logically own a `T`.
    //
    // For details, see:
    // https://github.com/rust-lang/rfcs/blob/master/text/0769-sound-generic-drop.md#phantom-data
    _marker: PhantomData<T>,
}

impl<T: ?Sized> Clone for Unique<T> {
    #[inline(always)]
    fn clone(&self) -> Self { *self }
}

impl<T: ?Sized> Copy for Unique<T> {}

/// `Unique` pointers are `Send` if `T` is `Send` because the data they
/// reference is unaliased. Note that this aliasing invariant is
/// unenforced by the type system; the abstraction using the
/// `Unique` must enforce it.
unsafe impl<T: Send + ?Sized> Send for Unique<T> { }

/// `Unique` pointers are `Sync` if `T` is `Sync` because the data they
/// reference is unaliased. Note that this aliasing invariant is
/// unenforced by the type system; the abstraction using the
/// `Unique` must enforce it.
unsafe impl<T: Sync + ?Sized> Sync for Unique<T> { }

impl<T: Sized> Unique<T> {
    /// Creates a new `Unique` that is dangling, but well-aligned.
    ///
    /// This is useful for initializing types which lazily allocate, like
    /// `Vec::new` does.
    pub const fn empty() -> Self {
        unsafe { Self::new_unchecked(mem::align_of::<T>() as *mut T) }
    }
}

impl<T: ?Sized> Unique<T> {
    /// Creates a new `Unique`.
    ///
    /// # Safety
    ///
    /// `ptr` must be non-null.
    pub const unsafe fn new_unchecked(ptr: *mut T) -> Self {
        Unique { pointer: ptr, _marker: PhantomData }
    }

    /// Creates a new `Unique` if `ptr` is non-null.
    pub fn new(ptr: *mut T) -> Option<Self> {
        if 0 == ptr as *mut () as usize { None }
        else { Some(unsafe { Self::new_unchecked(ptr) }) }
    }

    /// Acquires the underlying `*mut` pointer.
    pub fn as_ptr(self) -> *mut T { self.pointer as _ }

    /// Dereferences the content.
    ///
    /// The resulting lifetime is bound to self so this behaves "as if"
    /// it were actually an instance of T that is getting borrowed. If a longer
    /// (unbound) lifetime is needed, use `&*my_ptr.ptr()`.
    pub unsafe fn as_ref(&self) -> &T { &*self.pointer }

    /// Mutably dereferences the content.
    ///
    /// The resulting lifetime is bound to self so this behaves "as if"
    /// it were actually an instance of T that is getting borrowed. If a longer
    /// (unbound) lifetime is needed, use `&mut *my_ptr.ptr()`.
    pub unsafe fn as_mut(&mut self) -> &mut T { &mut *(self.pointer as *mut T) }
}

impl<T: ?Sized> fmt::Pointer for Unique<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Pointer::fmt(&self.pointer, f)
    }
}

impl<'a, T: ?Sized> From<&'a mut T> for Unique<T> {
    fn from(reference: &'a mut T) -> Self {
        Unique { pointer: reference, _marker: PhantomData }
    }
}

impl<'a, T: ?Sized> From<&'a T> for Unique<T> {
    fn from(reference: &'a T) -> Self {
        Unique { pointer: reference, _marker: PhantomData }
    }
}

/// `*mut T` but non-zero and covariant.
///
/// This is often the correct thing to use when building data structures using
/// raw pointers, but is ultimately more dangerous to use because of its additional
/// properties. If you're not sure if you should use `Shared<T>`, just use `*mut T`!
///
/// Unlike `*mut T`, the pointer must always be non-null, even if the pointer
/// is never dereferenced. This is so that enums may use this forbidden value
/// as a discriminant -- `Option<Shared<T>>` has the same size as `Shared<T>`.
/// However the pointer may still dangle if it isn't dereferenced.
///
/// Unlike `*mut T`, `Shared<T>` is covariant over `T`. If this is incorrect
/// for your use case, you should include some PhantomData in your type to
/// provide invariance, such as `PhantomData<Cell<T>>` or `PhantomData<&'a mut T>`.
/// Usually this won't be necessary; covariance is correct for most safe abstractions,
/// such as Box, Rc, Arc, Vec, and LinkedList. This is the case because they
/// provide a public API that follows the normal shared XOR mutable rules of Rust.
#[allow(missing_debug_implementations)]
pub struct Shared<T: ?Sized> {
    pointer: *const T,
}

impl<T: Sized> Shared<T> {
    /// Creates a new `Shared` that is dangling, but well-aligned.
    ///
    /// This is useful for initializing types which lazily allocate, like
    /// `Vec::new` does.
    pub const fn empty() -> Self {
        unsafe { Self::new_unchecked(mem::align_of::<T>() as *mut T) }
    }
}

impl<T: ?Sized> Shared<T> {
    /// Creates a new `Shared`.
    ///
    /// # Safety
    ///
    /// `ptr` must be non-null.
    pub const unsafe fn new_unchecked(ptr: *mut T) -> Self { Shared { pointer: ptr } }

    /// Creates a new `Shared` if `ptr` is non-null.
    pub fn new(ptr: *mut T) -> Option<Self> { Unique::new(ptr).map(Self::from) }

    /// Acquires the underlying `*mut` pointer.
    pub fn as_ptr(self) -> *mut T { self.pointer as _ }

    /// Dereferences the content.
    ///
    /// The resulting lifetime is bound to self so this behaves "as if"
    /// it were actually an instance of T that is getting borrowed. If a longer
    /// (unbound) lifetime is needed, use `&*my_ptr.ptr()`.
    pub unsafe fn as_ref(&self) -> &T { &*self.pointer }

    /// Mutably dereferences the content.
    ///
    /// The resulting lifetime is bound to self so this behaves "as if"
    /// it were actually an instance of T that is getting borrowed. If a longer
    /// (unbound) lifetime is needed, use `&mut *my_ptr.ptr_mut()`.
    pub unsafe fn as_mut(&mut self) -> &mut T { &mut *(self.pointer as *mut T) }
}

impl<T: ?Sized> Clone for Shared<T> {
    #[inline(always)]
    fn clone(&self) -> Self { *self }
}

impl<T: ?Sized> Copy for Shared<T> {}

impl<T: ?Sized> fmt::Pointer for Shared<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Pointer::fmt(&self.as_ptr(), f)
    }
}

impl<T: ?Sized> From<Unique<T>> for Shared<T> {
    fn from(unique: Unique<T>) -> Self { Shared { pointer: unique.pointer } }
}

impl<'a, T: ?Sized> From<&'a mut T> for Shared<T> {
    fn from(reference: &'a mut T) -> Self {
        Shared { pointer: reference }
    }
}

impl<'a, T: ?Sized> From<&'a T> for Shared<T> {
    fn from(reference: &'a T) -> Self {
        Shared { pointer: reference }
    }
}
