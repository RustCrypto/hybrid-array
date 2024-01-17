# [RustCrypto]: Hybrid Const Generic / Typenum Arrays

[![crate][crate-image]][crate-link]
[![Docs][docs-image]][docs-link]
[![Build Status][build-image]][build-link]
![Apache2/MIT licensed][license-image]
![Rust Version][rustc-image]
[![Project Chat][chat-image]][chat-link]

Hybrid array type combining const generics with the expressiveness of
[`typenum`]-based constraints, providing an alternative to [`generic-array`]
and a incremental transition path to const generics.

## About

This crate uses `typenum` to enable the following features which aren't yet
possible with the stable implementation of const generics:

- [#60551: Associated constants in traits can not be used in const generics][rust-issue-60551]
- [#76560: Complex generic constants: `feature(generic_const_exprs)`][rust-issue-76560]

Internally the crate is built on const generics and provides traits which make
it possible to convert between const generic types and `typenum` types.

## Features

This crate exposes the following feature flags. The default is NO features.

* `zeroize` - Implements [`Zeroize`](https://docs.rs/zeroize/latest/zeroize/trait.Zeroize.html) for `Array<T: Zeroize, U>`

## Migrating from `GenericArray`

*NOTE: this guide assumes a migration from `generic-array` v0.14*

`hybrid-array` has been designed to largely be a drop-in replacement for
`generic-array`, albeit with a public inner array type and significantly less
`unsafe` code.

Migrating should hopefully be relatively painless with the following
substitutions in your `.rs` files:

- Replace `generic_array` with `hybrid_array`
- Replace `GenericArray<T, U>` with `Array<T, U>`
- Replace `ArrayLength<T>` with `ArraySize`
- Replace `<U as ArrayLength<T>>::ArrayType` with `<U as ArraySize>::ArrayType<T>`
- Replace usages of the `arr![N; A, B, C]` macro with `Array([A, B, C])`

If you have any questions, please [start a discussion].

## License

Licensed under either of:

 * [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0)
 * [MIT license](http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[//]: # (badges)

[crate-image]: https://buildstats.info/crate/hybrid-array
[crate-link]: https://crates.io/crates/hybrid-array
[docs-image]: https://docs.rs/hybrid-array/badge.svg
[docs-link]: https://docs.rs/hybrid-array/
[build-image]: https://github.com/RustCrypto/utils/workflows/hybrid-array/badge.svg
[build-link]: https://github.com/RustCrypto/utils/actions/workflows/hybrid-array.yml
[license-image]: https://img.shields.io/badge/license-Apache2.0/MIT-blue.svg
[rustc-image]: https://img.shields.io/badge/rustc-1.65+-blue.svg
[chat-image]: https://img.shields.io/badge/zulip-join_chat-blue.svg
[chat-link]: https://rustcrypto.zulipchat.com/#narrow/stream/260052-utils

[//]: # (links)

[RustCrypto]: https://github.com/rustcrypto
[RustCrypto/utils#378]: https://github.com/RustCrypto/utils/issues/378
[`typenum`]: https://github.com/paholg/typenum
[`generic-array`]: https://github.com/fizyk20/generic-array
[rust-issue-60551]: https://github.com/rust-lang/rust/issues/60551
[rust-issue-76560]: https://github.com/rust-lang/rust/issues/76560
[start a discussion]: https://github.com/RustCrypto/hybrid-array/discussions
