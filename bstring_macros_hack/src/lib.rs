//! Uses the `proc-macro-hack` crate to implement `bstring` macros

extern crate proc_macro;
#[macro_use] extern crate proc_macro_hack;

extern crate bstring;
#[macro_use] extern crate quote;
extern crate syn;

use std::slice::Iter;

use bstring::{bstr, BString};
use bstring::bfmt::{Item, Parser};
use quote::{Tokens, ToTokens};
use syn::{Delimited, DelimToken, Ident, Lit, Token, TokenTree};

proc_macro_expr_impl!{
    pub fn bformat_args_impl(input: &str) -> String {
        let input = syn::parse_token_trees(input)
            .expect("parse_token_trees");

        let expr = if detect_keywords(&input) {
            bformat_keys(&input)
        } else {
            bformat_args(&input)
        };

        expr.to_string()
    }
}

fn bformat_args(input: &[TokenTree]) -> Tokens {
    let mut args = input.iter();

    // Evaluated expressions
    let mut exprs = Vec::new();
    // Expression idents, assigned by match statement
    let mut expr_ident = Vec::new();
    // Ident name counter
    let mut ident_idx = 0;

    let format = get_format(&mut args);

    while let Some(expr) = next_arg(&mut args) {
        let ident = Ident::from(format!("__arg{}", ident_idx));
        ident_idx += 1;

        exprs.push(expr);
        expr_ident.push(ident);
    }

    // Explicitly borrow
    let expr_ident = &expr_ident;

    let mut args_used = vec![false; exprs.len()];

    // Text pieces of format string
    let mut fmt_strs = Vec::new();
    // Current format string text piece
    let mut cur_fmt = BString::new();
    // Argument idents
    let mut arg_idents = Vec::new();
    let mut next_arg = 0;
    let mut p = Parser::new(format);

    loop {
        let item = match p.next() {
            Ok(item) => item,
            Err(e) => panic!("invalid format string: {}", e)
        };

        match item {
            Item::End => break,
            Item::Escape(b) => cur_fmt.push(b),
            Item::Text(s) => cur_fmt.push_str(s),
            Item::Field => {
                fmt_strs.push(cur_fmt.into_bytes());
                cur_fmt = BString::new();
                use_arg(next_arg, &mut args_used, &mut arg_idents, expr_ident);
                next_arg += 1;
            }
            Item::Name(name) => {
                if let Ok(n) = name.parse::<usize>() {
                    fmt_strs.push(cur_fmt.into_bytes());
                    cur_fmt = BString::new();
                    use_arg(n, &mut args_used, &mut arg_idents, expr_ident);
                } else {
                    panic!("invalid reference to argument `{}` \
                        (cannot mix named and positional arguments)",
                        name.to_string_lossy());
                }
            }
        }
    }

    if !cur_fmt.is_empty() {
        fmt_strs.push(cur_fmt.into_bytes());
    }

    if let Some(pos) = args_used.iter().position(|used| !used) {
        panic!("unused field in position `{}`", pos);
    }

    quote!{
        ::bstring::bfmt::Arguments::new_v1(
            {
                static __STATIC_BFMTSTR: &'static [&'static [u8]] =
                    &[#(&#fmt_strs),*];
                unsafe { ::std::mem::transmute::<_, &[&::bstring::bstr]>(__STATIC_BFMTSTR) }
            },
            &match (#(&#exprs , )*) {
                (#(#expr_ident , )*) =>
                    [#(::bstring::bfmt::ArgumentV1::new(#arg_idents,
                        ::bstring::bfmt::Display::bfmt)),*]
            })
    }
}

fn use_arg<'a>(n: usize, used: &mut Vec<bool>,
        arg_idents: &mut Vec<&'a Ident>, idents: &'a [Ident]) {
    if n >= idents.len() {
        panic!("invalid reference to argument `{}`", n);
    }

    used[n] = true;
    arg_idents.push(&idents[n]);
}

fn bformat_keys(input: &[TokenTree]) -> Tokens {
    let mut args = input.iter();

    // Evaluated expressions
    let mut exprs = Vec::new();
    // Expression idents, assigned by match statement
    let mut expr_ident = Vec::new();
    // Ident name counter
    let mut ident_idx = 0;
    // Argument name, used
    let mut arg_names: Vec<(&bstr, bool)> = Vec::new();

    let format = get_format(&mut args);

    while let Some((name, expr)) = next_kw_pair(&mut args) {
        exprs.push(expr);
        arg_names.push((name.as_ref(), false));
        expr_ident.push(Ident::from(format!("__arg{}", ident_idx)));
        ident_idx += 1;
    }

    // Explicitly borrow
    let expr_ident = &expr_ident;

    // Text pieces of format string
    let mut fmt_strs = Vec::new();
    // Current format string text piece
    let mut cur_fmt = BString::new();
    // Argument idents
    let mut arg_idents = Vec::new();
    let mut p = Parser::new(format);

    loop {
        let item = match p.next() {
            Ok(item) => item,
            Err(e) => panic!("invalid format string: {}", e)
        };

        match item {
            Item::End => break,
            Item::Escape(b) => cur_fmt.push(b),
            Item::Text(s) => cur_fmt.push_str(s),
            Item::Field => {
                panic!("invalid reference to argument \
                    (cannot mix named and positional arguments)");
            }
            Item::Name(name) => {
                fmt_strs.push(cur_fmt.into_bytes());
                cur_fmt = BString::new();
                use_kw_arg(name, &mut arg_names, &mut arg_idents, &expr_ident);
            }
        }
    }

    if !cur_fmt.is_empty() {
        fmt_strs.push(cur_fmt.into_bytes());
    }

    if let Some(&(name, _)) = arg_names.iter().find(|&&(_, used)| !used) {
        panic!("unused argument `{}`", name.to_string_lossy());
    }

    quote!{
        ::bstring::bfmt::Arguments::new_v1(
            {
                static __STATIC_BFMTSTR: &'static [&'static [u8]] =
                    &[#(&#fmt_strs),*];
                unsafe { ::std::mem::transmute::<_, &[&::bstring::bstr]>(__STATIC_BFMTSTR) }
            },
            &match (#(&#exprs , )*) {
                (#(#expr_ident , )*) =>
                    [#(::bstring::bfmt::ArgumentV1::new(#arg_idents,
                        ::bstring::bfmt::Display::bfmt)),*]
            })
    }
}

fn use_kw_arg<'a>(name: &bstr, names: &mut Vec<(&bstr, bool)>,
        arg_idents: &mut Vec<&'a Ident>, idents: &'a [Ident]) {
    match names.iter().position(|&(n, _)| name == n) {
        Some(pos) => {
            names[pos].1 = true;
            arg_idents.push(&idents[pos]);
        }
        None => {
            panic!("invalid reference to argument `{}`", name.to_string_lossy())
        }
    }
}

fn detect_keywords(input: &[TokenTree]) -> bool {
    let mut iter = input.iter();

    // Format string
    let _ = iter.next();
    // Comma
    let _ = iter.next();

    match iter.next() {
        Some(&TokenTree::Token(Token::Ident(_))) => (),
        _ => return false
    }

    match iter.next() {
        Some(&TokenTree::Token(Token::Eq)) => true,
        _ => false
    }
}

fn expected_comma(tok: &TokenTree) -> ! {
    panic!("expected comma, found `{}`", tok_str(tok));
}

fn unexpected_end() -> ! {
    panic!("unexpected end of macro invocation");
}

fn get_format<'a>(iter: &mut Iter<'a, TokenTree>) -> &'a bstr {
    match iter.next() {
        Some(&TokenTree::Token(Token::Literal(Lit::Str(ref s, _)))) => s.as_ref(),
        Some(&TokenTree::Token(Token::Literal(Lit::ByteStr(ref s, _)))) => s.as_ref(),
        Some(tok) => panic!("expected format string; found: `{}`", tok_str(tok)),
        None => unexpected_end()
    }
}

fn consume_comma(iter: &mut Iter<TokenTree>) -> bool {
    match iter.clone().next() {
        Some(&TokenTree::Token(Token::Comma)) => {
            let _ = iter.next();
            true
        }
        _ => false
    }
}

fn next_arg(iter: &mut Iter<TokenTree>) -> Option<TokenTree> {
    if !consume_comma(iter) {
        if let Some(tok) = iter.next() {
            expected_comma(tok);
        }
    }

    next_expr(iter)
}

fn next_kw_pair<'a>(iter: &mut Iter<'a, TokenTree>) -> Option<(&'a str, TokenTree)> {
    if !consume_comma(iter) {
        if let Some(tok) = iter.next() {
            expected_comma(tok);
        }
    }

    let name = match iter.next() {
        Some(&TokenTree::Token(Token::Ident(ref ident))) => ident.as_ref(),
        Some(tok) => panic!("expected ident; found: `{}`", tok_str(tok)),
        None => return None
    };

    match iter.next() {
        Some(&TokenTree::Token(Token::Eq)) => (),
        Some(tok) => panic!("expected `=`; found: `{}`", tok_str(tok)),
        None => unexpected_end()
    }

    let expr = match next_expr(iter) {
        Some(tt) => tt,
        None => unexpected_end()
    };

    Some((name, expr))
}

fn next_expr(iter: &mut Iter<TokenTree>) -> Option<TokenTree> {
    let first = match iter.next() {
        Some(tok) => tok,
        None => return None
    };

    match iter.clone().next() {
        Some(&TokenTree::Token(Token::Comma)) | None =>
            return Some(first.clone()),
        _ => ()
    }

    let mut tts = Vec::new();

    tts.push(first.clone());

    loop {
        match iter.clone().next() {
            Some(&TokenTree::Token(Token::Comma)) | None => break,
            Some(tok) => {
                let _ = iter.next();
                tts.push(tok.clone());
            }
        }
    }

    Some(TokenTree::Delimited(Delimited{
        delim: DelimToken::Paren,
        tts: tts,
    }))
}

fn tok_str<T: ToTokens>(tok: &T) -> String {
    let mut tokens = Tokens::new();
    tok.to_tokens(&mut tokens);
    tokens.to_string()
}
