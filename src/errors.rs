use semver::{self, Identifier};
use std::{self, error, fmt, io, str};

/// The error type for this crate.
#[derive(Debug)]
pub enum Error {
    /// An error occurred when executing the `rustc` command.
    CouldNotExecuteCommand(io::Error),
    /// The output of `rustc -vV` was not valid utf-8.
    Utf8Error(str::Utf8Error),
    /// The output of `rustc -vV` was not in the expected format.
    UnexpectedVersionFormat,
    /// An error occurred in parsing a `VersionReq`.
    ReqParseError(semver::ReqParseError),
    /// An error occurred in parsing the semver.
    SemVerError(semver::SemVerError),
    /// The pre-release tag is unknown.
    UnknownPreReleaseTag(Identifier),
}
use Error::*;

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            CouldNotExecuteCommand(ref e) => write!(f, "could not execute command: {}", e),
            Utf8Error(_) => write!(f, "invalid UTF-8 output from `rustc -vV`"),
            UnexpectedVersionFormat => write!(f, "unexpected `rustc -vV` format"),
            ReqParseError(ref e) => write!(f, "error parsing version requirement: {}", e),
            SemVerError(ref e) => write!(f, "error parsing version: {}", e),
            UnknownPreReleaseTag(ref i) => write!(f, "unknown pre-release tag: {}", i),
        }
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match *self {
            CouldNotExecuteCommand(ref e) => Some(e),
            Utf8Error(ref e) => Some(e),
            UnexpectedVersionFormat => None,
            ReqParseError(ref e) => Some(e),
            SemVerError(ref e) => Some(e),
            UnknownPreReleaseTag(_) => None,
        }
    }
}

macro_rules! impl_from {
    ($($err_ty:ty => $variant:ident),* $(,)*) => {
        $(
            impl From<$err_ty> for Error {
                fn from(e: $err_ty) -> Error {
                    Error::$variant(e)
                }
            }
        )*
    }
}

impl_from! {
    str::Utf8Error => Utf8Error,
    semver::SemVerError => SemVerError,
    semver::ReqParseError => ReqParseError,
}

/// The result type for this crate.
pub type Result<T> = std::result::Result<T, Error>;
