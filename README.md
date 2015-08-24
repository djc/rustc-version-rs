rustc-version-rs
==============

[![Travis-CI Status](https://travis-ci.org/Kimundi/rustc-version-rs.png?branch=master)](https://travis-ci.org/Kimundi/rustc-version-rs)

A library for querying the version of a installed rustc compiler.

For more details, see the [docs](http://kimundi.github.io/rustc-version-rs/rustc_version/index.html).

# Getting Started

[rustc-version-rs is available on crates.io](https://crates.io/crates/rustc_version).
Add the following dependency to your Cargo manifest to get the latest version of the 0.1 branch:
```toml
[dependencies]

rustc_version = "0.1.*"
```

To always get the latest version, add this git repository to your
Cargo manifest:

```toml
[dependencies.rustc_version]
git = "https://github.com/Kimundi/rustc-version-rs"
```
# Example

```rust
extern crate rustc_version;

fn main() {

}
```
