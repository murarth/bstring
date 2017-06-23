# `bstring`

The `bstring` crate provides two types, `bstr` and `BString`,
which implement `str`-like functions for byte strings with unknown encoding.

The `bstring_macros` crate provides the `bformat!` macro,
which implements byte string formatting, similar to `format!`.

These types are intended to assist when implementing text-based protocols
with no set character encoding.

[`bstring` documentation](https://docs.rs/bstring/)

[`bstring_macros` documentation](https://docs.rs/bstring_macros/)

## Building

To include `bstring` in your project, add the following to your `Cargo.toml`:

```toml
[dependencies]
bstring = "0.1"
bstring_macros = "0.1"
```

And the following to your crate root:

```rust
extern crate bstring;
#[macro_use] extern crate bstring_macros;
```

## License

`bstring` is distributed under the terms of both the MIT license and the
Apache License (Version 2.0).

See LICENSE-APACHE and LICENSE-MIT for details.
