# `nodejs-semver`

This crate is a pure Rust-based implementation of JavaScript's
[`node-semver`](https://npm.im/semver). That is, it's designed to be
compatible with Node/NPM's particular flavor of semver (which the [`semver`
crate](https://crates.io/crates/semver) is not).

It is designed for Rust programs and libraries meant for JavaScript tooling,
and does its best to stay compatible with `node-semver`.

It also supports [`serde`](https://crates.io/crates/serde) serialization,
converting versions and ranges to strings.

This project has been forked from [node-semver](https://github.com/felipesere/node-semver-rs) since September of 2023, but a lot has changed.

## Usage

`nodejs-semver` includes two main types: [Version] and [Range]. See [the
documentation](https://docs.rs/nodejs-semver) for more details.:

```rust
use nodejs_semver::{Range, Version};

let version: Version = "1.2.3".parse().unwrap();
let range: Range = "^1.2".parse().unwrap();

assert!(version.satisfies(&range));
```
