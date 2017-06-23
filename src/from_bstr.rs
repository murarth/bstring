//! Provides the `FromBStr` trait, used to parse values from `&bstr`

use std::fmt;
use std::str::FromStr;

use bstring::bstr;

/// Parses a value from a `&bstr`, much like `FromStr` parses from `&str`.
pub trait FromBStr: Sized {
    /// Error type returned from a failed parsing attempt.
    type Err;

    /// Parses a `bstr` to return this value.
    fn from_bstr(b: &bstr) -> Result<Self, Self::Err>;
}

/// Indicates a failure to parse a value through the `FromStr` trait
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum FromStrError<T> {
    /// Invalid UTF-8; `&bstr` could not be converted to `&str`
    InvalidUtf8,
    /// Failed to parse value
    ParseError(T)
}

impl<T> FromStrError<T> {
    /// Returns a borrowed reference to the wrapped error `T`.
    ///
    /// Returns `None` if the error is `InvalidUtf8`.
    #[inline]
    pub fn as_inner(&self) -> Option<&T> {
        match *self {
            FromStrError::ParseError(ref t) => Some(t),
            _ => None
        }
    }

    /// Returns the wrapped error `T`.
    ///
    /// Returns `None` if the error is `InvalidUtf8`.
    #[inline]
    pub fn into_inner(self) -> Option<T> {
        match self {
            FromStrError::ParseError(t) => Some(t),
            _ => None
        }
    }
}

impl<T: fmt::Display> fmt::Display for FromStrError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FromStrError::InvalidUtf8 => f.write_str("invalid utf-8"),
            FromStrError::ParseError(ref e) => e.fmt(f)
        }
    }
}

impl<T: FromStr> FromBStr for T {
    type Err = FromStrError<<T as FromStr>::Err>;

    fn from_bstr(b: &bstr) -> Result<T, FromStrError<<Self as FromStr>::Err>> {
        b.to_str().map_err(|_| FromStrError::InvalidUtf8)
            .and_then(|s| s.parse().map_err(FromStrError::ParseError))
    }
}
