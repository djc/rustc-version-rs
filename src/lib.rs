// Copyright 2016 rustc-version-rs developers
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![warn(missing_docs)]
#![allow(clippy::match_like_matches_macro)]

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

extern crate semver;
use semver::Identifier;
use std::process::Command;
use std::{env, fmt, str};
use std::{ffi::OsString, str::FromStr};

// Convenience re-export to allow version comparison without needing to add
// semver crate.
pub use semver::Version;

mod errors;
pub use errors::{Error, LlvmVersionParseError, Result};

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
        if let Some(part) = parts.next().transpose()? {
            minor = part;
            if major >= 4 && minor != 0 {
                // only LLVM versions earlier than 4.0 can have non-zero minor versions
                return Err(LlvmVersionParseError::MinorVersionMustBeZeroAfter4);
            }
        } else if major < 4 {
            // LLVM versions earlier than 4.0 have significant minor versions, so require the minor version in this case.
            return Err(LlvmVersionParseError::MinorVersionRequiredBefore4);
        }
        if parts.next().transpose()?.is_some() {
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

#[test]
fn rustc_error() {
    let mut cmd = Command::new("rustc");
    cmd.arg("--FOO");
    let stderr = match VersionMeta::for_command(cmd) {
        Err(Error::CommandError { stdout: _, stderr }) => stderr,
        _ => panic!("command error expected"),
    };
    assert_eq!(stderr, "error: Unrecognized option: \'FOO\'\n\n");
}

#[test]
fn smoketest() {
    let v = version().unwrap();
    assert!(v.major >= 1);

    let v = version_meta().unwrap();
    assert!(v.semver.major >= 1);

    assert!(version().unwrap() >= Version::parse("1.0.0").unwrap());
}

#[test]
fn parse_unexpected() {
    let res = version_meta_for(
        "rustc 1.0.0 (a59de37e9 2015-05-13) (built 2015-05-14)
binary: rustc
commit-hash: a59de37e99060162a2674e3ff45409ac73595c0e
commit-date: 2015-05-13
rust-birthday: 2015-05-14
host: x86_64-unknown-linux-gnu
release: 1.0.0",
    );

    assert!(match res {
        Err(Error::UnexpectedVersionFormat) => true,
        _ => false,
    });
}

#[test]
fn parse_1_0_0() {
    let version = version_meta_for(
        "rustc 1.0.0 (a59de37e9 2015-05-13) (built 2015-05-14)
binary: rustc
commit-hash: a59de37e99060162a2674e3ff45409ac73595c0e
commit-date: 2015-05-13
build-date: 2015-05-14
host: x86_64-unknown-linux-gnu
release: 1.0.0",
    )
    .unwrap();

    assert_eq!(version.semver, Version::parse("1.0.0").unwrap());
    assert_eq!(
        version.commit_hash,
        Some("a59de37e99060162a2674e3ff45409ac73595c0e".into())
    );
    assert_eq!(version.commit_date, Some("2015-05-13".into()));
    assert_eq!(version.build_date, Some("2015-05-14".into()));
    assert_eq!(version.channel, Channel::Stable);
    assert_eq!(version.host, "x86_64-unknown-linux-gnu");
    assert_eq!(
        version.short_version_string,
        "rustc 1.0.0 (a59de37e9 2015-05-13) (built 2015-05-14)"
    );
    assert_eq!(version.llvm_version, None);
}

#[test]
fn parse_unknown() {
    let version = version_meta_for(
        "rustc 1.3.0
binary: rustc
commit-hash: unknown
commit-date: unknown
host: x86_64-unknown-linux-gnu
release: 1.3.0",
    )
    .unwrap();

    assert_eq!(version.semver, Version::parse("1.3.0").unwrap());
    assert_eq!(version.commit_hash, None);
    assert_eq!(version.commit_date, None);
    assert_eq!(version.channel, Channel::Stable);
    assert_eq!(version.host, "x86_64-unknown-linux-gnu");
    assert_eq!(version.short_version_string, "rustc 1.3.0");
    assert_eq!(version.llvm_version, None);
}

#[test]
fn parse_nightly() {
    let version = version_meta_for(
        "rustc 1.5.0-nightly (65d5c0833 2015-09-29)
binary: rustc
commit-hash: 65d5c083377645a115c4ac23a620d3581b9562b6
commit-date: 2015-09-29
host: x86_64-unknown-linux-gnu
release: 1.5.0-nightly",
    )
    .unwrap();

    assert_eq!(version.semver, Version::parse("1.5.0-nightly").unwrap());
    assert_eq!(
        version.commit_hash,
        Some("65d5c083377645a115c4ac23a620d3581b9562b6".into())
    );
    assert_eq!(version.commit_date, Some("2015-09-29".into()));
    assert_eq!(version.channel, Channel::Nightly);
    assert_eq!(version.host, "x86_64-unknown-linux-gnu");
    assert_eq!(
        version.short_version_string,
        "rustc 1.5.0-nightly (65d5c0833 2015-09-29)"
    );
    assert_eq!(version.llvm_version, None);
}

#[test]
fn parse_stable() {
    let version = version_meta_for(
        "rustc 1.3.0 (9a92aaf19 2015-09-15)
binary: rustc
commit-hash: 9a92aaf19a64603b02b4130fe52958cc12488900
commit-date: 2015-09-15
host: x86_64-unknown-linux-gnu
release: 1.3.0",
    )
    .unwrap();

    assert_eq!(version.semver, Version::parse("1.3.0").unwrap());
    assert_eq!(
        version.commit_hash,
        Some("9a92aaf19a64603b02b4130fe52958cc12488900".into())
    );
    assert_eq!(version.commit_date, Some("2015-09-15".into()));
    assert_eq!(version.channel, Channel::Stable);
    assert_eq!(version.host, "x86_64-unknown-linux-gnu");
    assert_eq!(
        version.short_version_string,
        "rustc 1.3.0 (9a92aaf19 2015-09-15)"
    );
    assert_eq!(version.llvm_version, None);
}

#[test]
fn parse_1_16_0_nightly() {
    let version = version_meta_for(
        "rustc 1.16.0-nightly (5d994d8b7 2017-01-05)
binary: rustc
commit-hash: 5d994d8b7e482e87467d4a521911477bd8284ce3
commit-date: 2017-01-05
host: x86_64-unknown-linux-gnu
release: 1.16.0-nightly
LLVM version: 3.9",
    )
    .unwrap();

    assert_eq!(version.semver, Version::parse("1.16.0-nightly").unwrap());
    assert_eq!(
        version.commit_hash,
        Some("5d994d8b7e482e87467d4a521911477bd8284ce3".into())
    );
    assert_eq!(version.commit_date, Some("2017-01-05".into()));
    assert_eq!(version.channel, Channel::Nightly);
    assert_eq!(version.host, "x86_64-unknown-linux-gnu");
    assert_eq!(
        version.short_version_string,
        "rustc 1.16.0-nightly (5d994d8b7 2017-01-05)"
    );
    assert_eq!(
        version.llvm_version,
        Some(LlvmVersion { major: 3, minor: 9 })
    );
}

#[test]
fn parse_1_47_0_stable() {
    let version = version_meta_for(
        "rustc 1.47.0 (18bf6b4f0 2020-10-07)
binary: rustc
commit-hash: 18bf6b4f01a6feaf7259ba7cdae58031af1b7b39
commit-date: 2020-10-07
host: powerpc64le-unknown-linux-gnu
release: 1.47.0
LLVM version: 11.0",
    )
    .unwrap();

    assert_eq!(version.semver, Version::parse("1.47.0").unwrap());
    assert_eq!(
        version.commit_hash,
        Some("18bf6b4f01a6feaf7259ba7cdae58031af1b7b39".into())
    );
    assert_eq!(version.commit_date, Some("2020-10-07".into()));
    assert_eq!(version.channel, Channel::Stable);
    assert_eq!(version.host, "powerpc64le-unknown-linux-gnu");
    assert_eq!(
        version.short_version_string,
        "rustc 1.47.0 (18bf6b4f0 2020-10-07)"
    );
    assert_eq!(
        version.llvm_version,
        Some(LlvmVersion {
            major: 11,
            minor: 0,
        })
    );
}

#[test]
fn parse_debian_buster() {
    let version = version_meta_for(
        "rustc 1.41.1
binary: rustc
commit-hash: unknown
commit-date: unknown
host: powerpc64le-unknown-linux-gnu
release: 1.41.1
LLVM version: 7.0",
    )
    .unwrap();

    assert_eq!(version.semver, Version::parse("1.41.1").unwrap());
    assert_eq!(version.commit_hash, None);
    assert_eq!(version.commit_date, None);
    assert_eq!(version.channel, Channel::Stable);
    assert_eq!(version.host, "powerpc64le-unknown-linux-gnu");
    assert_eq!(version.short_version_string, "rustc 1.41.1");
    assert_eq!(
        version.llvm_version,
        Some(LlvmVersion { major: 7, minor: 0 })
    );
}

#[test]
fn parse_termux() {
    let version = version_meta_for(
        "rustc 1.46.0
binary: rustc
commit-hash: unknown
commit-date: unknown
host: aarch64-linux-android
release: 1.46.0
LLVM version: 10.0",
    )
    .unwrap();

    assert_eq!(version.semver, Version::parse("1.46.0").unwrap());
    assert_eq!(version.commit_hash, None);
    assert_eq!(version.commit_date, None);
    assert_eq!(version.channel, Channel::Stable);
    assert_eq!(version.host, "aarch64-linux-android");
    assert_eq!(version.short_version_string, "rustc 1.46.0");
    assert_eq!(
        version.llvm_version,
        Some(LlvmVersion {
            major: 10,
            minor: 0,
        })
    );
}

#[test]
fn parse_llvm_version_empty() {
    let res: Result<LlvmVersion, _> = "".parse();
    assert!(match res {
        Err(LlvmVersionParseError::ParseIntError(_)) => true,
        _ => false,
    });
}

#[test]
fn parse_llvm_version_invalid_char() {
    let res: Result<LlvmVersion, _> = "A".parse();
    assert!(match res {
        Err(LlvmVersionParseError::ParseIntError(_)) => true,
        _ => false,
    });
}

#[test]
fn parse_llvm_version_overflow() {
    let res: Result<LlvmVersion, _> = "9999999999999999999999999999999".parse();
    assert!(match res {
        Err(LlvmVersionParseError::ParseIntError(_)) => true,
        _ => false,
    });
}

#[test]
fn parse_llvm_version_leading_zero_on_zero() {
    let res: Result<LlvmVersion, _> = "00".parse();
    assert!(match res {
        Err(LlvmVersionParseError::ComponentMustNotHaveLeadingZeros) => true,
        _ => false,
    });
}

#[test]
fn parse_llvm_version_leading_zero_on_nonzero() {
    let res: Result<LlvmVersion, _> = "01".parse();
    assert!(match res {
        Err(LlvmVersionParseError::ComponentMustNotHaveLeadingZeros) => true,
        _ => false,
    });
}

#[test]
fn parse_llvm_version_3_components() {
    let res: Result<LlvmVersion, _> = "4.0.0".parse();

    assert!(match res {
        Err(LlvmVersionParseError::TooManyComponents) => true,
        _ => false,
    });
}

#[test]
fn parse_llvm_version_4_components() {
    let res: Result<LlvmVersion, _> = "4.0.0.0".parse();

    assert!(match res {
        Err(LlvmVersionParseError::TooManyComponents) => true,
        _ => false,
    });
}

#[test]
fn parse_llvm_version_component_sign_plus() {
    let res: Result<LlvmVersion, _> = "1.+3".parse();

    assert!(match res {
        Err(LlvmVersionParseError::ComponentMustNotHaveSign) => true,
        _ => false,
    });
}

#[test]
fn parse_llvm_version_component_sign_minus() {
    let res: Result<LlvmVersion, _> = "1.-3".parse();

    assert!(match res {
        Err(LlvmVersionParseError::ComponentMustNotHaveSign) => true,
        _ => false,
    });
}

#[test]
fn parse_llvm_version_3() {
    let res: Result<LlvmVersion, _> = "3".parse();

    assert!(match res {
        Err(LlvmVersionParseError::MinorVersionRequiredBefore4) => true,
        _ => false,
    });
}

#[test]
fn parse_llvm_version_4_1() {
    let res: Result<LlvmVersion, _> = "4.1".parse();

    assert!(match res {
        Err(LlvmVersionParseError::MinorVersionMustBeZeroAfter4) => true,
        _ => false,
    });
}

#[test]
fn parse_llvm_version_5() {
    let v: LlvmVersion = "5".parse().unwrap();
    assert_eq!(v, LlvmVersion { major: 5, minor: 0 });
}

#[test]
fn parse_llvm_version_5_0() {
    let v: LlvmVersion = "5.0".parse().unwrap();
    assert_eq!(v, LlvmVersion { major: 5, minor: 0 });
}

#[test]
fn parse_llvm_version_4_0() {
    let v: LlvmVersion = "4.0".parse().unwrap();
    assert_eq!(v, LlvmVersion { major: 4, minor: 0 });
}

#[test]
fn parse_llvm_version_3_0() {
    let v: LlvmVersion = "3.0".parse().unwrap();
    assert_eq!(v, LlvmVersion { major: 3, minor: 0 });
}

#[test]
fn parse_llvm_version_3_9() {
    let v: LlvmVersion = "3.9".parse().unwrap();
    assert_eq!(v, LlvmVersion { major: 3, minor: 9 });
}

#[test]
fn parse_llvm_version_11_0() {
    let v: LlvmVersion = "11.0".parse().unwrap();
    assert_eq!(
        v,
        LlvmVersion {
            major: 11,
            minor: 0
        }
    );
}

#[test]
fn parse_llvm_version_11() {
    let v: LlvmVersion = "11".parse().unwrap();
    assert_eq!(
        v,
        LlvmVersion {
            major: 11,
            minor: 0
        }
    );
}

#[test]
fn test_llvm_version_comparison() {
    // check that field order is correct
    assert!(LlvmVersion { major: 3, minor: 9 } < LlvmVersion { major: 4, minor: 0 });
}

/*
#[test]
fn version_matches_replacement() {
    let f = |s1: &str, s2: &str| {
        let a = Version::parse(s1).unwrap();
        let b = Version::parse(s2).unwrap();
        println!("{} <= {} : {}", s1, s2, a <= b);
    };

    println!();

    f("1.5.0",         "1.5.0");
    f("1.5.0-nightly", "1.5.0");
    f("1.5.0",         "1.5.0-nightly");
    f("1.5.0-nightly", "1.5.0-nightly");

    f("1.5.0",         "1.6.0");
    f("1.5.0-nightly", "1.6.0");
    f("1.5.0",         "1.6.0-nightly");
    f("1.5.0-nightly", "1.6.0-nightly");

    panic!();

}
*/
