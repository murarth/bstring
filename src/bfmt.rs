//! Byte string formatting
//!
//! This module is analogous to the standard [`fmt`][fmt] module, but is
//! more limited in scope.
//!
//! There is only one trait, [`Display`][display], and formatting flags
//! are not currently supported.
//!
//! However, `bformat!` is able to use the result of the standard macro
//! [`format_args!`][format_args] to produce formatted byte string.
//!
//! ```ignore
//! bformat!("foo {}",
//!     format_args!("{:x}", 255))
//! ```
//!
//! [display]: trait.Display.html
//! [fmt]: https://doc.rust-lang.org/std/fmt/
//! [format_args]: https://doc.rust-lang.org/std/macro.format_args.html

use std::borrow::Cow;
use std::cmp::min;
use std::fmt;
use std::mem::transmute;
use std::rc::Rc;
use std::sync::Arc;

use bstring::{bstr, BString};

struct Void {}

/// Represents a formatted string and set of arguments.
///
/// A value of this struct can be generated using the `bformat_args!` macro
/// from the `bstring_macros` crate. You should never need to construct one
/// of these directly.
#[derive(Copy, Clone)]
pub struct Arguments<'a> {
    fmt: &'a [&'a bstr],
    args: &'a [ArgumentV1<'a>],
}

impl<'a> Arguments<'a> {
    /// Constructs a new set of text components and formatted arguments.
    ///
    /// Text components and arguments are printed, alternating, until either
    /// one is exhausted.
    ///
    /// A value of this struct can be generated using the `bformat_args!` macro
    /// from the `bstring_macros` crate. You should never need to construct one
    /// of these directly.
    #[inline]
    pub fn new_v1(fmt: &'a [&'a bstr], args: &'a [ArgumentV1<'a>]) -> Arguments<'a> {
        Arguments{
            fmt: fmt,
            args: args,
        }
    }
}

/// Represents a formatted argument.
///
/// A set of values of this struct can be generated using the `bformat_args!`
/// macro from the `bstring_macros` crate. You should never need to construct
/// one of these directly.
#[derive(Copy)]
pub struct ArgumentV1<'a> {
    value: &'a Void,
    display: fn(&Void, &mut Formatter) -> Result,
}

impl<'a> Clone for ArgumentV1<'a> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a> ArgumentV1<'a> {
    /// Constructs a new formatted argument from a value and a display function.
    #[inline]
    pub fn new<T>(value: &'a T, display: fn(&T, &mut Formatter) -> Result) -> ArgumentV1<'a> {
        ArgumentV1{
            value: unsafe { transmute(value) },
            display: unsafe { transmute(display) },
        }
    }
}

/// Formats an `Arguments` value into a `BString`.
#[inline]
pub fn format_args(args: Arguments) -> BString {
    let mut fmter = Formatter::new();

    fmter.write_fmt(args)
        .expect("a formatting trait returned an error");

    fmter.into_bstring()
}

/// Parses a `&bstr` format string into a series of `Item` components.
#[derive(Clone)]
pub struct Parser<'a> {
    orig: &'a bstr,
    rest: &'a bstr,
    pos: usize,
}

/// Represents an error parsing a format string.
#[derive(Debug)]
pub struct ParseError {
    /// Kind of error encountered
    pub kind: ParseErrorKind,
    /// Offset of format string at which the error was encountered
    pub index: usize,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} at index {}", self.kind.description(), self.index)
    }
}

/// Represents a kind of error generated while parsing a format string.
#[derive(Copy, Clone, Debug)]
pub enum ParseErrorKind {
    /// An open brace (`{`) was found without a matching close brace (`}`)
    MissingCloseBrace,
    /// A close brace (`}`) was found without a matching open brace (`{`)
    UnmatchedCloseBrace,
}

impl ParseErrorKind {
    /// Returns a description of the error.
    #[inline]
    pub fn description(&self) -> &'static str {
        match *self {
            ParseErrorKind::MissingCloseBrace => "missing close brace",
            ParseErrorKind::UnmatchedCloseBrace => "unmatched close brace",
        }
    }
}

impl<'a> Parser<'a> {
    /// Creates a new parser for the given format string.
    #[inline]
    pub fn new(fmt: &bstr) -> Parser {
        Parser{
            orig: fmt,
            rest: fmt,
            pos: 0,
        }
    }

    /// Returns the next item of the format string.
    ///
    /// If an error is encountered, it is returned.
    ///
    /// When the end of the format string is reached,
    /// `Ok(Item::End)` is returned.
    #[inline]
    pub fn next(&mut self) -> ::std::result::Result<Item<'a>, ParseError> {
        if self.rest.is_empty() {
            return Ok(Item::End);
        }

        let (item, end) = if self.rest.starts_with("{{") {
            (Item::Escape(b'{'), 2)
        } else if self.rest.starts_with("}}") {
            (Item::Escape(b'}'), 2)
        } else if self.rest.starts_with("}") {
            return Err(ParseError{
                kind: ParseErrorKind::UnmatchedCloseBrace,
                index: self.pos
            });
        } else if self.rest.starts_with("{") {
            match self.rest.find(b'}') {
                Some(1) => (Item::Field, 2),
                Some(n) => (Item::Name(&self.rest[1..n]), n + 1),
                None => return Err(ParseError{
                    kind: ParseErrorKind::MissingCloseBrace,
                    index: self.pos,
                })
            }
        } else {
            let open = self.rest.find(b'{');
            let close = self.rest.find(b'}');

            let pos = match (open, close) {
                (Some(a), Some(b)) => min(a, b),
                (Some(n), None) | (None, Some(n)) => n,
                (None, None) => self.rest.len()
            };

            (Item::Text(&self.rest[..pos]), pos)
        };

        self.rest = &self.rest[end..];
        self.pos += end;

        Ok(item)
    }
}

/// Represents a section of a parsed format string.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Item<'a> {
    /// End of format string
    End,
    /// Escaped character, `{` or `}`
    Escape(u8),
    /// Plain text component
    Text(&'a bstr),
    /// Field component without a name `{}`
    Field,
    /// Field component with name or index, e.g. `{0}` or `{foo}`
    Name(&'a bstr),
}

/// Byte string formatter
pub struct Formatter {
    bytes: BString,
}

impl Formatter {
    fn new() -> Formatter {
        Formatter{
            bytes: BString::new(),
        }
    }

    fn into_bstring(self) -> BString {
        self.bytes
    }

    /// Writes a `&bstr` value to the formatter.
    ///
    /// This function always succeeds, returning `Ok(())`.
    #[inline]
    pub fn write<S: AsRef<bstr>>(&mut self, buf: S) -> Result {
        self.bytes.push_str(buf);
        Ok(())
    }

    /// Write formatted arguments to the formatter.
    pub fn write_fmt<T: WriteFmt>(&mut self, fmt: T) -> Result {
        fmt.write_fmt(self)
    }
}

/// Helper trait to support `Formatter::write_fmt`
///
/// This trait is implemented by the `bstring` struct `Arguments`
/// and the standard struct of the same name.
pub trait WriteFmt: Sized {
    /// Write formatted arguments to the formatter.
    fn write_fmt(self, f: &mut Formatter) -> Result;
}

impl<'a> WriteFmt for fmt::Arguments<'a> {
    fn write_fmt(self, f: &mut Formatter) -> Result {
        fmt::Write::write_fmt(&mut FmtWrite(f), self).map_err(|_| Error)
    }
}

impl<'a> WriteFmt for Arguments<'a> {
    fn write_fmt(self, f: &mut Formatter) -> Result {
        let mut fmt = self.fmt.iter();
        let mut arg = self.args.iter();

        loop {
            let fmt = match fmt.next() {
                Some(s) => s,
                None => break
            };

            f.write(fmt)?;

            let arg = match arg.next() {
                Some(a) => a,
                None => break
            };

            (arg.display)(arg.value, f)?;
        }

        Ok(())
    }
}

/// Represents an error returned from a formatting trait
#[derive(Debug)]
pub struct Error;

/// The `Result` type returned from the `bfmt` formatting trait.
pub type Result = ::std::result::Result<(), Error>;

/// Displays a value using a formatter.
pub trait Display {
    /// Formats the value using the given formatter.
    fn bfmt(&self, f: &mut Formatter) -> Result;
}

/// Creates a `BString` from a value.
pub trait ToBString {
    /// Returns a `BString` for the value.
    fn to_bstring(&self) -> BString;
}

impl<T: ?Sized + Display> ToBString for T {
    fn to_bstring(&self) -> BString {
        let mut fmter = Formatter::new();

        self.bfmt(&mut fmter)
            .expect("a formatter trait implementation returned an error");

        let mut bs = fmter.into_bstring();
        bs.shrink_to_fit();

        bs
    }
}

impl<'a, T: ?Sized + Display> Display for &'a T {
    fn bfmt(&self, f: &mut Formatter) -> Result {
        (**self).bfmt(f)
    }
}

impl<'a, T: ?Sized + Display> Display for &'a mut T {
    fn bfmt(&self, f: &mut Formatter) -> Result {
        (**self).bfmt(f)
    }
}

impl<T: ?Sized + Display> Display for Box<T> {
    fn bfmt(&self, f: &mut Formatter) -> Result {
        (**self).bfmt(f)
    }
}

impl<T: ?Sized + Display> Display for Rc<T> {
    fn bfmt(&self, f: &mut Formatter) -> Result {
        (**self).bfmt(f)
    }
}

impl<T: ?Sized + Display> Display for Arc<T> {
    fn bfmt(&self, f: &mut Formatter) -> Result {
        (**self).bfmt(f)
    }
}

impl Display for [u8] {
    fn bfmt(&self, f: &mut Formatter) -> Result {
        f.write(self)
    }
}

impl Display for bstr {
    fn bfmt(&self, f: &mut Formatter) -> Result {
        f.write(self)
    }
}

impl Display for BString {
    fn bfmt(&self, f: &mut Formatter) -> Result {
        f.write(self)
    }
}

impl<'a, T: ?Sized> Display for Cow<'a, T>
        where T: Display + ToOwned, <T as ToOwned>::Owned: Display {
    fn bfmt(&self, f: &mut Formatter) -> Result {
        match *self {
            Cow::Borrowed(ref b) => b.bfmt(f),
            Cow::Owned(ref o) => o.bfmt(f)
        }
    }
}

struct FmtWrite<'a>(&'a mut Formatter);

impl<'a> fmt::Write for FmtWrite<'a> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0.write(s).map_err(|_| fmt::Error)
    }
}

macro_rules! impl_display {
    ( $( $ty:ty , )+ ) => {
        $(
            impl Display for $ty {
                fn bfmt(&self, f: &mut Formatter) -> Result {
                    f.write_fmt(format_args!("{}", self))
                }
            }
        )*
    }
}

// Manually implement Display for some standard `fmt::Display` types.
// A blanket impl would cause a conflict.
impl_display!{
    bool, char,
    str, String,
    f32, f64,
    i8, i16, i32, i64, isize,
    u8, u16, u32, u64, usize,
    ::std::char::ToLowercase,
    ::std::char::ToUppercase,
    ::std::net::IpAddr,
    ::std::net::Ipv4Addr,
    ::std::net::Ipv6Addr,
    ::std::net::SocketAddr,
    ::std::net::SocketAddrV4,
    ::std::net::SocketAddrV6,
}

impl<T: Display> Display for ::std::num::Wrapping<T> {
    fn bfmt(&self, f: &mut Formatter) -> Result {
        self.0.bfmt(f)
    }
}

impl<'a> Display for fmt::Arguments<'a> {
    fn bfmt(&self, f: &mut Formatter) -> Result {
        f.write_fmt(*self)
    }
}

impl<'a> Display for Arguments<'a> {
    fn bfmt(&self, f: &mut Formatter) -> Result {
        f.write_fmt(*self)
    }
}

#[cfg(test)]
mod test {
    use super::{Item, Parser, ParseError, ParseErrorKind};

    #[test]
    fn test_bformat_iter() {
        let mut p = Parser::new("foo {bar} {{baz}} {}".as_ref());

        assert_matches!(p.next().unwrap(), Item::Text(s) if s == "foo ");
        assert_matches!(p.next().unwrap(), Item::Name(s) if s == "bar");
        assert_matches!(p.next().unwrap(), Item::Text(s) if s == " ");
        assert_matches!(p.next().unwrap(), Item::Escape(b'{'));
        assert_matches!(p.next().unwrap(), Item::Text(s) if s == "baz");
        assert_matches!(p.next().unwrap(), Item::Escape(b'}'));
        assert_matches!(p.next().unwrap(), Item::Text(s) if s == " ");
        assert_matches!(p.next().unwrap(), Item::Field);
        assert_matches!(p.next().unwrap(), Item::End);
    }

    #[test]
    fn test_bformat_error() {
        let mut p = Parser::new("foo {bar".as_ref());

        assert_matches!(p.next().unwrap(), Item::Text(s) if s == "foo ");
        assert_matches!(p.next().unwrap_err(), ParseError{
            kind: ParseErrorKind::MissingCloseBrace,
            index: 4,
        });

        let mut p = Parser::new("foo }".as_ref());

        assert_matches!(p.next().unwrap(), Item::Text(s) if s == "foo ");
        assert_matches!(p.next().unwrap_err(), ParseError{
            kind: ParseErrorKind::UnmatchedCloseBrace,
            index: 4,
        });
    }
}
