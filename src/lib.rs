//! Byte string formatting and manipulation
//!
//! This crate provides the types [`bstr`][bstr] and [`BString`][bstring],
//! which implement `str`-like functions for byte string values with
//! unknown encoding.
//!
//! These types are intended to assist when implementing text-based protocols
//! with no set character encoding.
//!
//! The [`bstring_macros`][macros] crate provides formatting macros,
//! similar to those found in the standard library for `String` values.
//!
//! [bstr]: bstring/struct.bstr.html
//! [bstring]: bstring/struct.BString.html
//! [macros]: https://docs.rs/bstring_macros/

#![deny(missing_docs)]

#[cfg(test)] #[macro_use] extern crate assert_matches;
extern crate ref_slice;

pub use bstring::{bstr, BString};
pub use from_bstr::FromBStr;
pub use bfmt::ToBString;

pub mod bfmt;
pub mod bstring;
pub mod from_bstr;
pub mod pattern;
