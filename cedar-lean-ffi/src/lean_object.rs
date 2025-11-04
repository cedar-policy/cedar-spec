/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//! Defines safe wrappers for working with Lean objects

use prost::Message;
use serde::Deserialize;
use std::{
    ffi::{c_char, c_uint, CStr},
    marker::PhantomData,
    str::Utf8Error,
};
use thiserror::Error;

use lean_sys::{
    lean_alloc_sarray, lean_ctor_get, lean_ctor_num_objs, lean_dec, lean_inc, lean_is_ctor,
    lean_is_string, lean_object, lean_ptr_tag, lean_sarray_object, lean_string_cstr,
};

use crate::FfiError;

#[derive(Debug, Error)]
pub enum LeanObjectError {
    #[error("expected a object tagged with {expected_one_of:?}, but saw tag {actual}")]
    UnexpectedConstructorTag {
        expected_one_of: Vec<u8>,
        actual: u8,
    },
    #[error("expected lean constructor object, but saw tag {0}")]
    ExpectedConstructor(u8),
    #[error("expected lean sting object, but saw tag {0}")]
    ExpectedString(u8),
    #[error("string could not be decoded as utf8: {0}")]
    Utf8Error(Utf8Error),
    #[error("constructor index out of bounds {idx}, constructor contains {num_objs} objects")]
    ConstructorIndexOutOfBounds { idx: c_uint, num_objs: c_uint },
}

/// Borrowed reference to a Lean object which we've confirmed is an inductive.
#[derive(Debug, Copy, Clone)]
pub struct LeanCtorObject<'a>(*mut lean_object, PhantomData<&'a OwnedLeanObject>);

impl<'a> LeanCtorObject<'a> {
    /// Get the number of objects stored in this objects. E.g.,  for a lean
    /// `Except` object, both constructors will have 1 object.
    pub fn num_objs(&self) -> c_uint {
        unsafe { lean_ctor_num_objs(self.0) }
    }

    /// Get an object out of this constructor, or returns `None` if the
    /// requested object index is out of bounds.
    pub fn get(&self, idx: c_uint) -> Result<LeanObject<'a>, LeanObjectError> {
        let num_objs = self.num_objs();
        if idx < num_objs {
            Ok(LeanObject(
                // This functions takes a `b_lean_obj_arg` and returns a
                // `b_lean_obj_res` so it is safe to pass it the borrowed
                // reference held in `self`. We return the result as a borrowed
                // lean object, assuming that it must have the same lifetime as `self`.
                unsafe { lean_ctor_get(self.0, idx) },
                PhantomData,
            ))
        } else {
            Err(LeanObjectError::ConstructorIndexOutOfBounds {
                idx: 0,
                num_objs: self.num_objs(),
            })
        }
    }

    /// View this object as a Rust `Result`, assuming that it is a Lean `Except`.
    /// Performs some error checking, returning a `FfiError`, if this object has
    /// fewer variants or fields than expected.
    pub fn as_result(&'_ self) -> Result<Result<LeanObject<'a>, LeanObject<'a>>, LeanObjectError> {
        match self.as_object().tag() {
            0 => self.get(0).map(Result::Err),
            1 => self.get(0).map(Result::Ok),
            n => Err(LeanObjectError::UnexpectedConstructorTag {
                expected_one_of: vec![0, 1],
                actual: n,
            }),
        }
    }

    /// Any inductive Lean object can be viewed as a regular Lean object.
    pub fn as_object(&self) -> LeanObject<'a> {
        LeanObject(self.0, PhantomData)
    }
}

/// Borrowed reference to a lean object.
#[derive(Debug, Copy, Clone)]
pub struct LeanObject<'a>(
    pub(crate) *mut lean_object,
    pub(crate) PhantomData<&'a OwnedLeanObject>,
);

impl<'a> LeanObject<'a> {
    /// Convert this borrowed Lean object to an owned object by incrementing the reference count.
    pub fn to_owned(&self) -> OwnedLeanObject {
        unsafe {
            lean_inc(self.0);
        }
        OwnedLeanObject(self.0)
    }

    /// Check if this object is an inductive
    pub fn is_ctor(&self) -> bool {
        unsafe { lean_is_ctor(self.0) }
    }

    /// Check if this object is a string
    pub fn is_string(&self) -> bool {
        unsafe { lean_is_string(self.0) }
    }

    /// Returns a view of this object as an inductive object, if it is one, otherwise returns `None`.
    pub fn as_ctor(&self) -> Option<LeanCtorObject<'a>> {
        self.is_ctor().then(|| LeanCtorObject(self.0, PhantomData))
    }

    /// Get the tag for this object, used to differentiate between constructors of inductive objects.
    pub fn tag(&self) -> u8 {
        unsafe { lean_ptr_tag(self.0) }
    }

    /// View this object as a Rust `Result`
    pub fn as_result(&'_ self) -> Result<Result<LeanObject<'a>, LeanObject<'a>>, LeanObjectError> {
        if let Some(ctor_obj) = self.as_ctor() {
            ctor_obj.as_result()
        } else {
            Err(LeanObjectError::ExpectedConstructor(self.tag()))
        }
    }

    /// View this `LeanObject` as a Rust `&str`, returns an error if this object is not a String.
    pub fn as_rust_str(&self) -> Result<&'a str, LeanObjectError> {
        if !self.is_string() {
            return Err(LeanObjectError::ExpectedString(self.tag()));
        }
        let cstr = unsafe {
            // note: `lean_string_cstr()` is declared to take `b_lean_obj_arg`
            // meaning that it takes a borrowed argument so it is correct to
            // pass the borrowed `self` here.
            let lean_obj_p = lean_string_cstr(self.0);
            CStr::from_ptr(lean_obj_p as *const c_char)
        };
        cstr.to_str().map_err(LeanObjectError::Utf8Error)
    }

    /// Deserialize this `LeanObject` into type `T`, assuming that it is a Lean
    /// string containing JSON in format `T`
    pub fn deserialize_into<T: Deserialize<'a>>(&self) -> Result<T, FfiError> {
        let str = self.as_rust_str()?;
        serde_json::from_str(str).map_err(|e| {
            FfiError::LeanDeserializationError(format!(
                "failed to deserialize object from Lean: {e}\nobject from Lean was: {str}"
            ))
        })
    }
}

/// Safe wrapper around `*mut lean_object`, which ensures that the Lean object
/// is freed when this Rust value is dropped. Only use this if the Rust code is
/// responsible for decrementing the reference count on the `lean_object` in
/// question.
#[derive(Debug)]
pub struct OwnedLeanObject(*mut lean_object);

impl Drop for OwnedLeanObject {
    fn drop(&mut self) {
        unsafe {
            lean_dec(self.0);
        }
    }
}

impl Clone for OwnedLeanObject {
    fn clone(&self) -> Self {
        unsafe {
            lean_inc(self.0);
        }
        OwnedLeanObject(self.0)
    }
}

impl OwnedLeanObject {
    /// Create an `OwnedLeanObject` with `buf` as its contents
    pub fn new_array_from_buf(buf: &[u8]) -> Self {
        unsafe {
            let x: *mut lean_sarray_object = lean_alloc_sarray(1, buf.len(), buf.len()).cast();
            let y = (*x).m_data.as_mut_ptr();
            for (i, bi) in buf.iter().enumerate() {
                y.add(i).write(*bi)
            }
            Self(x.cast())
        }
    }

    /// Obtain a borrowed lean object from this owned object
    pub fn as_borrowed<'a>(&'a self) -> LeanObject<'a> {
        LeanObject(self.0, PhantomData)
    }
}

/// Call a Lean FFI function that is assumed to take a single Lean object as
/// argument and return a single Lean object as the return value.
/// Assumes that Rust is responsible for eventually decrementing the
/// reference count on the returned Lean object.
/// Assumes that Lean "takes ownership" of `arg`, that is, Rust should not
/// decrement the reference count on `arg` itself after passing it to `func`.
pub unsafe fn call_lean_ffi_function(
    func: unsafe extern "C" fn(*mut lean_object) -> *mut lean_object,
    arg: OwnedLeanObject,
) -> OwnedLeanObject {
    let ret = OwnedLeanObject(func(arg.0));
    // Since `func` "takes ownership" of `arg`, we need to not decrement the
    // refcount on `arg` ourselves when it is dropped. So we `mem::forget` it to
    // prevent the `Drop` impl from running. Effectively, Lean has dropped it
    // for us.
    std::mem::forget(arg);
    ret
}

pub unsafe fn call_lean_ffi_bi_function(
    func: unsafe extern "C" fn(*mut lean_object, *mut lean_object) -> *mut lean_object,
    arg0: OwnedLeanObject,
    arg1: OwnedLeanObject,
) -> OwnedLeanObject {
    let ret = OwnedLeanObject(func(arg0.0, arg1.0));
    // Since `func` "takes ownership" of `arg`, we need to not decrement the
    // refcount on `arg` ourselves when it is dropped. So we `mem::forget` it to
    // prevent the `Drop` impl from running. Effectively, Lean has dropped it
    // for us.
    std::mem::forget(arg0);
    std::mem::forget(arg1);
    ret
}

/// Call a Lean FFI function that is assumed to take a Protobuf message as
/// argument
pub unsafe fn call_lean_ffi_takes_protobuf(
    func: unsafe extern "C" fn(*mut lean_object) -> *mut lean_object,
    arg: &impl Message,
) -> OwnedLeanObject {
    let arg = OwnedLeanObject::new_array_from_buf(&arg.encode_to_vec());
    call_lean_ffi_function(func, arg)
}

pub unsafe fn call_lean_ffi_takes_obj_and_protobuf(
    func: unsafe extern "C" fn(*mut lean_object, *mut lean_object) -> *mut lean_object,
    arg0: OwnedLeanObject,
    arg1: &impl Message,
) -> OwnedLeanObject {
    let arg1 = OwnedLeanObject::new_array_from_buf(&arg1.encode_to_vec());
    call_lean_ffi_bi_function(func, arg0, arg1)
}
