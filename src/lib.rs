#![no_std]

extern crate core;

use core::{fmt, mem};

/// A pointer and boolean bitpacked together.
///
/// [`PtrBool`]s are the same size as a raw pointer; four bytes on a 32-bit system and eight bytes
/// on a 64-bit system.  This is done by storing in the boolean value in the one-bit of the
/// pointer.
///
/// # Caveats
/// * The pointer must be aligned by two to ensure that the one-bit is unnecessary and can be used
///   to stored the boolean value.
///
/// * Possibly a slight overhead when reading the values of the [`PtrBool`], as the boolean value
///   must be omitted from the pointer *each time it's read*, and the pointer value must be omitted
///   from the boolean value each time it is read.  That is, unless there is some sort of unknown
///   optimization built into Rust for the case of storing a boolean in one bit.
///
/// * The value stored inside of a [`PtrBool`] must be [`Sized`].  This is because the pointer is
///   converted to and from a [`usize`]; which loses any metadata which would have been in the raw
///   pointer.
#[derive(Clone, Copy, PartialEq)]
#[repr(transparent)]
pub struct PtrBool<T> {
    inner: *mut T,
}

impl<T> PtrBool<T> {
    /// Returns the raw pointer value, omitting the boolean value.
    #[inline]
    fn get_ptr(&self) -> *mut T {
        (self.inner as usize & !1) as *mut T
    }

    /// Returns the raw boolean value, omitting the pointer value.
    #[inline]
    fn get_bool(&self) -> bool {
        self.inner as usize & 1 == 1
    }
}

impl<T> PtrBool<T> {
    /// Initializes a [`PtrBool`] from the provided pointer and boolean values if the pointer is
    /// aligned by two.
    ///
    /// # Examples
    /// ```
    /// use ptr_bool::PtrBool;
    ///
    /// let mut my_value = 42;
    /// let ptr = PtrBool::new(&mut my_value as *mut _, true).unwrap();
    ///
    /// assert_eq!(ptr.as_bool(), true);
    /// unsafe {
    ///     assert_eq!(*ptr.as_ref().unwrap(), 42);
    /// }
    /// ```
    pub fn new(mut ptr: *mut T, bool_: bool) -> Option<Self> {
        // Check the alignment of the pointer.
        if ptr as usize % 2 != 0 || mem::align_of::<T>() <= 1 {
            return None;
        }

        if bool_ {
            ptr = (ptr as usize | 1) as *mut T;
        }

        Some(Self { inner: ptr })
    }

    /// Initializes a [`PtrBool`] with a null pointer and the provided boolean value.  Returns
    /// `None` if the type of this [`PtrBool`] is not aligned by 2.
    ///
    /// # Examples
    /// ```
    /// use ptr_bool::PtrBool;
    ///
    /// let ptr: PtrBool<usize> = PtrBool::null(true).unwrap();
    ///
    /// assert_eq!(ptr.as_bool(), true);
    /// assert_eq!(ptr.is_null(), true);
    /// ```
    pub fn null(bool_: bool) -> Option<Self> {
        PtrBool::new(core::ptr::null::<T>() as *mut T, bool_)
    }

    /// Converts this [`PtrBool`] into a boolean value.
    ///
    /// # Examples
    /// ```
    /// use ptr_bool::PtrBool;
    ///
    /// let ptr: PtrBool<usize> = PtrBool::null(true).unwrap();
    ///
    /// assert_eq!(ptr.as_bool(), true);
    /// ```
    pub fn as_bool(&self) -> bool {
        self.get_bool()
    }

    /// Sets the inner boolean value of this pointer.
    ///
    /// # Examples
    /// ```
    /// use ptr_bool::PtrBool;
    ///
    /// let mut ptr: PtrBool<usize> = PtrBool::null(true).unwrap();
    ///
    /// assert_eq!(ptr.as_bool(), true);
    /// ptr.set_bool(false);
    /// assert_eq!(ptr.as_bool(), false);
    /// ```
    pub fn set_bool(&mut self, bool_: bool) {
        self.inner = (self.get_ptr() as usize | if bool_ == true { 1 } else { 0 }) as *mut T;
    }

    /// Converts this [`PtrBool`] into a raw pointer.
    ///
    /// # Examples
    /// ```
    /// use ptr_bool::PtrBool;
    /// use std::ptr;
    ///
    /// let mut ptr: PtrBool<usize> = PtrBool::null(true).unwrap();
    ///
    /// assert_eq!(ptr.as_ptr(), ptr::null());
    /// ```
    pub fn as_ptr(&self) -> *const T {
        self.get_ptr()
    }

    /// Converts this [`PtrBool`] into a raw mutable pointer.
    ///
    /// # Examples
    /// ```
    /// use ptr_bool::PtrBool;
    /// use std::ptr;
    ///
    /// let mut ptr: PtrBool<usize> = PtrBool::null(true).unwrap();
    ///
    /// assert_eq!(ptr.as_mut_ptr(), ptr::null_mut());
    /// ```
    pub fn as_mut_ptr(&self) -> *mut T {
        self.get_ptr()
    }

    /// Returns `true` if the internal pointer is null.
    ///
    /// # Examples
    /// ```
    /// use ptr_bool::PtrBool;
    /// use std::ptr;
    ///
    /// let mut ptr: PtrBool<usize> = PtrBool::null(true).unwrap();
    ///
    /// assert_eq!(ptr.is_null(), true);
    /// ```
    pub fn is_null(&self) -> bool {
        self.get_ptr().is_null()
    }

    /// Converts this [`PtrBool`] into a reference.
    ///
    /// # Safety
    /// By calling this method you promise that:
    ///
    /// * The wrapped pointer must be properly aligned.
    ///
    /// * This pointer must be dereferenceable in the sense defined in
    ///   [the `ptr` documentation](core::ptr).
    ///
    /// * The pointer must point to an initialized instance of `T`.
    ///
    /// * You must enforce Rust's aliasing rules, since the returned lifetime `'a` is arbitrarily
    ///   chosen and does not necessarily reflect the actual lifetime of the data. In particular,
    ///   while this reference exists, the memory the pointer points to must not get mutated
    ///   (except inside `UnsafeCell`).
    ///
    /// If you are completely sure this pointer is not null; then the
    /// [`as_ref_unchecked`](#method.as_ref_unchecked) method can be used instead.
    ///
    /// # Examples
    /// ```
    /// use ptr_bool::PtrBool;
    ///
    /// let raw_ptr = Box::into_raw(Box::new(42));
    /// let ptr_bool = PtrBool::new(raw_ptr, true).unwrap();
    ///
    /// unsafe { assert_eq!(*ptr_bool.as_ref().unwrap(), 42) };
    /// assert_eq!(ptr_bool.as_bool(), true);
    ///
    /// unsafe { Box::from_raw(ptr_bool.as_mut_ptr()) };
    /// ```
    pub unsafe fn as_ref<'a>(&self) -> Option<&'a T> {
        self.get_ptr().as_ref()
    }

    /// Converts this [`PtrBool`] into a reference.  Equivalent to `&*ptr_bool.as_mut_ptr()` in
    /// terms of safety.
    ///
    /// # Safety
    /// By calling this method you promise that:
    ///
    /// * The wrapped pointer must be properly aligned.
    ///
    /// * This pointer must be dereferenceable in the sense defined in
    ///   [the `ptr` documentation](core::ptr).
    ///
    /// * The pointer must point to an initialized instance of `T`.
    ///
    /// * You must enforce Rust's aliasing rules, since the returned lifetime `'a` is arbitrarily
    ///   chosen and does not necessarily reflect the actual lifetime of the data. In particular,
    ///   while this reference exists, the memory the pointer points to must not get mutated
    ///   (except inside `UnsafeCell`).
    ///
    /// If this pointer may be null, use the [`as_ref`](#method.as_ref) method instead.
    ///
    /// # Examples
    /// ```
    /// use ptr_bool::PtrBool;
    ///
    /// let raw_ptr = Box::into_raw(Box::new(42));
    /// let ptr_bool = PtrBool::new(raw_ptr, true).unwrap();
    ///
    /// unsafe { assert_eq!(*ptr_bool.as_ref_unchecked(), 42) };
    /// assert_eq!(ptr_bool.as_bool(), true);
    ///
    /// unsafe { Box::from_raw(ptr_bool.as_mut_ptr()) };
    /// ```
    pub unsafe fn as_ref_unchecked<'a>(&self) -> &'a T {
        &*self.get_ptr()
    }

    /// Converts this [`PtrBool`] into a reference.
    ///
    /// # Safety
    /// By calling this method you promise that:
    ///
    /// * The wrapped pointer must be properly aligned.
    ///
    /// * This pointer must be dereferenceable in the sense defined in
    ///   [the `ptr` documentation](core::ptr).
    ///
    /// * The pointer must point to an initialized instance of `T`.
    ///
    /// * You must enforce Rust's aliasing rules, since the returned lifetime `'a` is
    ///   arbitrarily chosen and does not necessarily reflect the actual lifetime of the data.
    ///   In particular, while this reference exists, the memory the pointer points to must
    ///   not get accessed (read or written) through any other pointer.
    ///
    /// If you are completely sure this pointer is not null; then the
    /// [`as_mut_unchecked`](#method.as_mut_unchecked) method can be used instead.
    ///
    /// # Examples
    /// ```
    /// use ptr_bool::PtrBool;
    ///
    /// let raw_ptr = Box::into_raw(Box::new(42));
    /// let ptr_bool = PtrBool::new(raw_ptr, true).unwrap();
    ///
    /// unsafe { assert_eq!(*ptr_bool.as_mut().unwrap(), 42) };
    /// assert_eq!(ptr_bool.as_bool(), true);
    ///
    /// unsafe { Box::from_raw(ptr_bool.as_mut_ptr()) };
    /// ```
    pub unsafe fn as_mut<'a>(&self) -> Option<&'a mut T> {
        self.get_ptr().as_mut()
    }

    /// Converts this [`PtrBool`] into a reference.  Equivalent to `&mut *ptr_bool.as_mut_ptr()` in
    /// terms of safety.
    ///
    /// # Safety
    /// By calling this method you promise that:
    ///
    /// * The wrapped pointer must be properly aligned.
    ///
    /// * This pointer must be dereferenceable in the sense defined in
    ///   [the `ptr` documentation](core::ptr).
    ///
    /// * The pointer must point to an initialized instance of `T`.
    ///
    /// * You must enforce Rust's aliasing rules, since the returned lifetime `'a` is
    ///   arbitrarily chosen and does not necessarily reflect the actual lifetime of the data.
    ///   In particular, while this reference exists, the memory the pointer points to must
    ///   not get accessed (read or written) through any other pointer.
    ///
    /// If this pointer may be null, use the [`as_mut`](#method.as_mut) method instead.
    ///
    /// # Examples
    /// ```
    /// use ptr_bool::PtrBool;
    ///
    /// let raw_ptr = Box::into_raw(Box::new(42));
    /// let ptr_bool = PtrBool::new(raw_ptr, true).unwrap();
    ///
    /// unsafe { assert_eq!(*ptr_bool.as_mut_unchecked(), 42) };
    /// assert_eq!(ptr_bool.as_bool(), true);
    ///
    /// unsafe { Box::from_raw(ptr_bool.as_mut_ptr()) };
    /// ```
    pub unsafe fn as_mut_unchecked<'a>(&self) -> &'a mut T {
        &mut *self.get_ptr()
    }
}

impl<T> fmt::Debug for PtrBool<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PtrBool")
            .field(&self.clone().get_ptr())
            .field(&self.clone().get_bool())
            .finish()
    }
}

impl<T> fmt::Display for PtrBool<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PtrBool")
            .field(&self.clone().get_ptr())
            .field(&self.clone().get_bool())
            .finish()
    }
}

impl<T> fmt::Pointer for PtrBool<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PtrBool")
            .field(&self.clone().get_ptr())
            .field(&self.clone().get_bool())
            .finish()
    }
}
