// Copyright 2016 rustc-version-rs developers
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![warn(missing_docs)]

//! Simple library for getting the version information of a `rustc`
//! compiler.
//!
//! This can be used by build scripts or other tools dealing with Rust sources
//! to make decisions based on the version of the compiler.
//!
//! It calls `$RUSTC --version -v` and parses the output, falling
//! back to `rustc` if `$RUSTC` is not set.
//!
//! # Example
//!
//! ```rust
//! // This could be a cargo build script
//!
//! extern crate rustc_version;
//! use rustc_version::{version, version_meta, Channel, Version};
//!
//! fn main() {
//!     // Assert we haven't travelled back in time
//!     assert!(version().unwrap().major >= 1);
//!
//!     // Set cfg flags depending on release channel
//!     match version_meta().unwrap().channel {
//!         Channel::Stable => {
//!             println!("cargo:rustc-cfg=RUSTC_IS_STABLE");
//!         }
//!         Channel::Beta => {
//!             println!("cargo:rustc-cfg=RUSTC_IS_BETA");
//!         }
//!         Channel::Nightly => {
//!             println!("cargo:rustc-cfg=RUSTC_IS_NIGHTLY");
//!         }
//!         Channel::Dev => {
//!             println!("cargo:rustc-cfg=RUSTC_IS_DEV");
//!         }
//!     }
//!
//!     // Check for a minimum version
//!     if version().unwrap() >= Version::parse("1.4.0").unwrap() {
//!         println!("cargo:rustc-cfg=compiler_has_important_bugfix");
//!     }
//! }
//! ```

#[cfg(test)]
#[macro_use]
extern crate doc_comment;

#[cfg(test)]
doctest!("../README.md");

use semver::Identifier;
use std::process::Command;
use std::{env, fmt, str};
use std::{ffi::OsString, str::FromStr};

// Convenience re-export to allow version comparison without needing to add
// semver crate.
pub use semver::Version;

mod errors;
pub use crate::errors::{Error, LlvmVersionParseError, Result};

/// Release channel of the compiler.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Channel {
    /// Development release channel
    Dev,
    /// Nightly release channel
    Nightly,
    /// Beta release channel
    Beta,
    /// Stable release channel
    Stable,
}

/// LLVM version
///
/// LLVM's version numbering scheme is not semver compatible until version 4.0
///
/// rustc [just prints the major and minor versions], so other parts of the version are not included.
///
/// [just prints the major and minor versions]: https://github.com/rust-lang/rust/blob/b5c9e2448c9ace53ad5c11585803894651b18b0a/compiler/rustc_codegen_llvm/src/llvm_util.rs#L173-L178
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct LlvmVersion {
    // fields must be ordered major, minor for comparison to be correct
    /// Major version
    pub major: u64,
    /// Minor version
    pub minor: u64,
}

impl fmt::Display for LlvmVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}", self.major, self.minor)
    }
}

impl FromStr for LlvmVersion {
    type Err = LlvmVersionParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut parts = s
            .split('.')
            .map(|part| -> Result<u64, LlvmVersionParseError> {
                if part == "0" {
                    Ok(0)
                } else if part.starts_with('0') {
                    Err(LlvmVersionParseError::ComponentMustNotHaveLeadingZeros)
                } else if part.starts_with('-') || part.starts_with('+') {
                    Err(LlvmVersionParseError::ComponentMustNotHaveSign)
                } else {
                    Ok(part.parse()?)
                }
            });

        let major = parts.next().unwrap()?;
        let mut minor = 0;

        if let Some(part) = parts.next() {
            minor = part?;
            if major >= 4 && minor != 0 {
                // only LLVM versions earlier than 4.0 can have non-zero minor versions
                return Err(LlvmVersionParseError::MinorVersionMustBeZeroAfter4);
            }
        } else if major < 4 {
            // LLVM versions earlier than 4.0 have significant minor versions, so require the minor version in this case.
            return Err(LlvmVersionParseError::MinorVersionRequiredBefore4);
        }

        if parts.next().is_some() {
            return Err(LlvmVersionParseError::TooManyComponents);
        }

        Ok(Self { major, minor })
    }
}

/// Rustc version plus metadata like git short hash and build date.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct VersionMeta {
    /// Version of the compiler
    pub semver: Version,

    /// Git short hash of the build of the compiler
    pub commit_hash: Option<String>,

    /// Commit date of the compiler
    pub commit_date: Option<String>,

    /// Build date of the compiler; this was removed between Rust 1.0.0 and 1.1.0.
    pub build_date: Option<String>,

    /// Release channel of the compiler
    pub channel: Channel,

    /// Host target triple of the compiler
    pub host: String,

    /// Short version string of the compiler
    pub short_version_string: String,

    /// Version of LLVM used by the compiler
    pub llvm_version: Option<LlvmVersion>,
}

impl VersionMeta {
    /// Returns the version metadata for `cmd`, which should be a `rustc` command.
    pub fn for_command(mut cmd: Command) -> Result<VersionMeta> {
        let out = cmd
            .arg("-vV")
            .output()
            .map_err(Error::CouldNotExecuteCommand)?;

        if !out.status.success() {
            return Err(Error::CommandError {
                stdout: String::from_utf8_lossy(&out.stdout).into(),
                stderr: String::from_utf8_lossy(&out.stderr).into(),
            });
        }

        version_meta_for(str::from_utf8(&out.stdout)?)
    }
}

/// Returns the `rustc` SemVer version.
pub fn version() -> Result<Version> {
    Ok(version_meta()?.semver)
}

/// Returns the `rustc` SemVer version and additional metadata
/// like the git short hash and build date.
pub fn version_meta() -> Result<VersionMeta> {
    let cmd = env::var_os("RUSTC").unwrap_or_else(|| OsString::from("rustc"));

    VersionMeta::for_command(Command::new(cmd))
}

/// Parses a "rustc -vV" output string and returns
/// the SemVer version and additional metadata
/// like the git short hash and build date.
pub fn version_meta_for(verbose_version_string: &str) -> Result<VersionMeta> {
    let out: Vec<_> = verbose_version_string.lines().collect();

    if !(out.len() >= 6 && out.len() <= 8) {
        return Err(Error::UnexpectedVersionFormat);
    }

    let short_version_string = out[0];

    #[allow(clippy::manual_strip)]
    fn expect_prefix<'a>(line: &'a str, prefix: &str) -> Result<&'a str> {
        if line.starts_with(prefix) {
            Ok(&line[prefix.len()..])
        } else {
            Err(Error::UnexpectedVersionFormat)
        }
    }

    let commit_hash = match expect_prefix(out[2], "commit-hash: ")? {
        "unknown" => None,
        hash => Some(hash.to_owned()),
    };

    let commit_date = match expect_prefix(out[3], "commit-date: ")? {
        "unknown" => None,
        hash => Some(hash.to_owned()),
    };

    // Handle that the build date may or may not be present.
    let mut idx = 4;
    let mut build_date = None;
    if out[idx].starts_with("build-date") {
        build_date = match expect_prefix(out[idx], "build-date: ")? {
            "unknown" => None,
            s => Some(s.to_owned()),
        };
        idx += 1;
    }

    let host = expect_prefix(out[idx], "host: ")?;
    idx += 1;
    let release = expect_prefix(out[idx], "release: ")?;
    idx += 1;
    let semver: Version = release.parse()?;

    let channel = if semver.pre.is_empty() {
        Channel::Stable
    } else {
        match semver.pre[0] {
            Identifier::AlphaNumeric(ref s) if s == "dev" => Channel::Dev,
            Identifier::AlphaNumeric(ref s) if s == "beta" => Channel::Beta,
            Identifier::AlphaNumeric(ref s) if s == "nightly" => Channel::Nightly,
            ref x => return Err(Error::UnknownPreReleaseTag(x.clone())),
        }
    };

    let llvm_version = if let Some(&line) = out.get(idx) {
        Some(expect_prefix(line, "LLVM version: ")?.parse()?)
    } else {
        None
    };

    Ok(VersionMeta {
        semver,
        commit_hash,
        commit_date,
        build_date,
        channel,
        host: host.into(),
        short_version_string: short_version_string.into(),
        llvm_version,
    })
}
