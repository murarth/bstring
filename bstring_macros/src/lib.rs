//! Provides formatting macros for byte strings
//!
//! This crate requires the `bstring` crate to be declared at the root level
//! of your crate:
//!
//! ```ignore
//! extern crate bstring;
//! #[macro_use] extern crate bstring_macros;
//! ```
//!
//! See [`bstring::bfmt`][bfmt] for more details.
//!
//! [bfmt]: https://docs.rs/bstring/*/bstring/bfmt/

#![deny(missing_docs)]

#[macro_use] extern crate proc_macro_hack;

#[allow(unused_imports)]
#[macro_use] extern crate bstring_macros_hack;

#[doc(hidden)]
pub use bstring_macros_hack::*;

extern crate bstring;

/// Formats a 
///
/// See 
#[macro_export]
macro_rules! bformat {
    ( $( $tt:tt )* ) => {
        ::bstring::bfmt::format_args(bformat_args!($($tt)*))
    }
}

proc_macro_expr_decl!{
    /// Produces a `bstring::Arguments` value, which can be passed to other
    /// formatting functions.
    ///
    /// The argument values passed to this macro are borrowed for the lifetime
    /// of the resulting `Arguments` value.
    bformat_args! => bformat_args_impl
}

#[cfg(test)]
mod test {
    use bstring::BString;
    use bstring::bfmt::Arguments;

    #[test]
    fn test_bformat_no_args() {
        let bs: BString = bformat!("Hello, world!");
        assert_eq!(bs, "Hello, world!");
    }

    #[test]
    fn test_bformat() {
        let a = "bar";
        let b = "baz";

        assert_eq!(bformat!("foo {}", a), "foo bar");
        assert_eq!(bformat!("foo {} baz", a), "foo bar baz");
        assert_eq!(bformat!("foo {} {}", a, b), "foo bar baz");

        assert_eq!(bformat!("foo {} {} {}", a, 123, b), "foo bar 123 baz");
    }

    #[test]
    fn test_bformat_boxes() {
        use std::rc::Rc;
        use std::sync::Arc;

        let a = "foo";
        let b = a.to_string();
        let c = Box::new(1);
        let d = Rc::new(2);
        let e = Arc::new(3);

        assert_eq!(bformat!("{} {} {}{}{}", a, b, c, d, e), "foo foo 123");
    }

    #[test]
    fn test_bformat_bytes() {
        assert_eq!(bformat!(b"\xff{}\xff", 123), b"\xff123\xff");
    }

    #[test]
    fn test_bformat_escape() {
        assert_eq!(bformat!("foo {{bar}}"), "foo {bar}");
    }

    #[test]
    fn test_bformat_named() {
        let a = "bar";
        let b = "baz";

        assert_eq!(bformat!("foo {bar}", bar = a), "foo bar");
        assert_eq!(bformat!("foo {bar} {baz}", bar = a, baz = b), "foo bar baz");
        assert_eq!(bformat!("foo {bar} {n} {baz}",
            bar = a, baz = b, n = 123), "foo bar 123 baz");
    }

    #[test]
    fn test_bformat_args() {
        // Workaround due to a limitation of proc-macro-hack.
        // This equivalent expression would fail to compile:
        //
        //      bformat!("sup {}", bformat_args!("{}", 123))
        fn fmt(args: Arguments) -> BString {
            bformat!("sup {}", args)
        }

        assert_eq!(fmt(bformat_args!("{}", 123)), "sup 123");
    }

    #[test]
    fn test_bformat_std_format() {
        assert_eq!(bformat!("sup {}", format_args!("{:02x}", 10)), "sup 0a");
    }
}
