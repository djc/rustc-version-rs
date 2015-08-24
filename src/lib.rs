#![warn(missing_docs)]

//! Simple library for getting the version information of a `rustc`
//! compiler.
//!
//! This simply calls `$RUSTC --version` and parses the output, falling
//! back to `rustc` if `$RUSTC` is not set.

extern crate semver;
use semver::{Version, VersionReq, Identifier};
use std::process::Command;
use std::env;

/// Release channel of the compiler.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Channel {
    /// Nightly release channel
    Nightly,
    /// Beta release channel
    Beta,
    /// Stable release channel
    Stable,
}

/// Rustc version plus metada like git short hash and build date.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct VersionMeta {
    /// Version of the compiler
    pub semver: Version,

    /// Git short hash of the build of the compiler
    pub git_short_hash: String,

    /// Build date of the compiler
    pub date: String,

    /// Release channel of the compiler
    pub channel: Channel
}

/// Returns the `rustc` SemVer version.
pub fn version() -> Version {
    version_meta().semver
}

/// Returns the `rustc` SemVer version and additional metadata
/// like the git short hash and build date.
pub fn version_meta() -> VersionMeta {
    let cmd = env::var("RUSTC").unwrap_or("rustc".into());

    let out = Command::new(&cmd)
        .arg("--version")
        .output()
        .unwrap_or_else(|e| { panic!("failed to execute process: {}", e) });

    let version_string = String::from_utf8(out.stdout).unwrap();
    let mut parts_iter = version_string.split_whitespace();

    let rustc_string = parts_iter.next().unwrap();
    assert!(rustc_string == "rustc");

    let version_string = parts_iter.next().unwrap();
    let version = Version::parse(version_string).unwrap();

    let hash_string = parts_iter.next().unwrap();
    assert!(hash_string.starts_with('('));
    let hash_string = &hash_string[1..];

    let date_string = parts_iter.next().unwrap();
    assert!(date_string.ends_with(')'));
    let date_string = &date_string[..date_string.len() - 1];

    let channel = if version.pre.is_empty() {
        Channel::Stable
    } else {
        match version.pre[0] {
            Identifier::AlphaNumeric(ref s)
                if s == "beta" => Channel::Beta,
            Identifier::AlphaNumeric(ref s)
                if s == "nightly" => Channel::Nightly,
            _ => panic!(),
        }
    };

    VersionMeta {
        semver: version,
        git_short_hash: hash_string.to_string(),
        date: date_string.to_string(),
        channel: channel,
    }
}

/// Check wether the `rustc` version matches the given SemVer
/// version requirement.
pub fn version_matches(req: &str) -> bool {
    VersionReq::parse(req).unwrap().matches(&version())
}

#[test]
fn smoketest() {
    let v = version();
    assert!(v.major >= 1);
    assert!(v.minor >= 2);

    let v = version_meta();
    assert!(v.semver.major >= 1);
    assert!(v.semver.minor >= 2);

    assert!(version_matches(">= 1.2.0"));
}
