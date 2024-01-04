use std::collections::{hash_set, HashSet};
use std::fmt;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use itertools::Itertools;
use config_proc_macro::config_type;
use serde::de::{SeqAccess, Visitor};
use serde::ser::SerializeSeq;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

// use crate::config::lists::*;
use crate::config::Config;

#[config_type]
pub enum NewlineStyle {
    /// Auto-detect based on the raw source input.
    Auto,
    /// Force CRLF (`\r\n`).
    Windows,
    /// Force CR (`\n`).
    Unix,
    /// `\r\n` in Windows, `\n` on other platforms.
    Native,
}

#[config_type]
/// Where to put the opening brace of items (`fn`, `impl`, etc.).
pub enum BraceStyle {
    /// Put the opening brace on the next line.
    AlwaysNextLine,
    /// Put the opening brace on the same line, if possible.
    PreferSameLine,
    /// Prefer the same line except where there is a where-clause, in which
    /// case force the brace to be put on the next line.
    SameLineWhere,
}

#[config_type]
/// Where to put the opening brace of conditional expressions (`if`, `match`, etc.).
pub enum ControlBraceStyle {
    /// K&R style
    AlwaysSameLine,
    /// Stroustrup style
    ClosingNextLine,
    /// Allman style
    AlwaysNextLine,
}

#[config_type]
/// How to indent.
pub enum IndentStyle {
    /// First line on the same line as the opening brace, all lines aligned with
    /// the first line.
    Visual,
    /// First line is on a new line and all lines align with **block** indent.
    Block,
}

#[config_type]
/// How to place a list-like items.
/// FIXME: Issue-3581: this should be renamed to ItemsLayout when publishing 2.0
pub enum Density {
    /// Fit as much on one line as possible.
    Compressed,
    /// Items are placed horizontally if sufficient space, vertically otherwise.
    Tall,
    /// Place every item on a separate line.
    Vertical,
}

#[config_type]
/// Spacing around type combinators.
pub enum TypeDensity {
    /// No spaces around "=" and "+"
    Compressed,
    /// Spaces around " = " and " + "
    Wide,
}

#[config_type]
/// Heuristic settings that can be used to simply
/// the configuration of the granular width configurations
/// like `struct_lit_width`, `array_width`, etc.
pub enum Heuristics {
    /// Turn off any heuristics
    Off,
    /// Turn on max heuristics
    Max,
    /// Use scaled values based on the value of `max_width`
    Default,
}

#[config_type]
/// Configuration for import groups, i.e. sets of imports separated by newlines.
pub enum GroupImportsTactic {
    /// Keep groups as they are.
    Preserve,
    /// Discard existing groups, and create new groups for
    ///  1. `std` / `core` / `alloc` imports
    ///  2. other imports
    ///  3. `self` / `crate` / `super` imports
    StdExternalCrate,
    /// Discard existing groups, and create a single group for everything
    One,
}

#[config_type]
/// How to merge imports.
pub enum ImportGranularity {
    /// Do not merge imports.
    Preserve,
    /// Use one `use` statement per crate.
    Crate,
    /// Use one `use` statement per module.
    Module,
    /// Use one `use` statement per imported item.
    Item,
    /// Use one `use` statement including all items.
    One,
}

/// Controls how movefmt should handle case in hexadecimal literals.
#[config_type]
pub enum HexLiteralCase {
    /// Leave the literal as-is
    Preserve,
    /// Ensure all literals use uppercase lettering
    Upper,
    /// Ensure all literals use lowercase lettering
    Lower,
}

#[config_type]
pub enum ReportTactic {
    Always,
    Unnumbered,
    Never,
}

/// What movefmt should emit. Mostly corresponds to the `--emit` command line
/// option.
#[config_type]
pub enum EmitMode {
    /// Emits to files.
    Files,
    /// Writes the output to stdout.
    Stdout,
    /// Checks if a diff can be generated. If so, movefmt outputs a diff and
    /// quits with exit code 1.
    /// This option is designed to be run in CI where a non-zero exit signifies
    /// non-standard code formatting. Used for `--check`.
    Diff,
}

/// Client-preference for coloured output.
#[config_type]
pub enum Color {
    /// Always use color, whether it is a piped or terminal output
    Always,
    /// Never use color
    Never,
    /// Automatically use color, if supported by terminal
    Auto,
}

#[config_type]
/// movefmt format style version.
pub enum Version {
    /// 1.x.y. When specified, movefmt will format in the same style as 1.0.0.
    One,
    /// 2.x.y. When specified, movefmt will format in the the latest style.
    Two,
}

impl Color {
    /// Whether we should use a coloured terminal.
    pub fn use_colored_tty(self) -> bool {
        match self {
            Color::Always | Color::Auto => true,
            Color::Never => false,
        }
    }
}

/// How chatty should movefmt be?
#[config_type]
pub enum Verbosity {
    /// Emit more.
    Verbose,
    /// Default.
    Normal,
    /// Emit as little as possible.
    Quiet,
}

impl Default for EmitMode {
    fn default() -> EmitMode {
        EmitMode::Files
    }
}

/// A set of directories, files and modules that movefmt should ignore.
#[derive(Default, Clone, Debug, PartialEq)]
pub struct IgnoreList {
    /// A set of path specified in movefmt.toml.
    path_set: HashSet<PathBuf>,
    /// A path to movefmt.toml.
    movefmt_toml_path: PathBuf,
}

impl fmt::Display for IgnoreList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}]",
            self.path_set
                .iter()
                .format_with(", ", |path, f| f(&format_args!(
                    "{}",
                    path.to_string_lossy()
                )))
        )
    }
}

impl Serialize for IgnoreList {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.path_set.len()))?;
        for e in &self.path_set {
            seq.serialize_element(e)?;
        }
        seq.end()
    }
}

impl<'de> Deserialize<'de> for IgnoreList {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct HashSetVisitor;
        impl<'v> Visitor<'v> for HashSetVisitor {
            type Value = HashSet<PathBuf>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a sequence of path")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'v>,
            {
                let mut path_set = HashSet::new();
                while let Some(elem) = seq.next_element()? {
                    path_set.insert(elem);
                }
                Ok(path_set)
            }
        }
        Ok(IgnoreList {
            path_set: deserializer.deserialize_seq(HashSetVisitor)?,
            movefmt_toml_path: PathBuf::new(),
        })
    }
}

impl<'a> IntoIterator for &'a IgnoreList {
    type Item = &'a PathBuf;
    type IntoIter = hash_set::Iter<'a, PathBuf>;

    fn into_iter(self) -> Self::IntoIter {
        self.path_set.iter()
    }
}

impl IgnoreList {
    pub fn add_prefix(&mut self, dir: &Path) {
        self.movefmt_toml_path = dir.to_path_buf();
    }

    pub fn movefmt_toml_path(&self) -> &Path {
        &self.movefmt_toml_path
    }
}

impl FromStr for IgnoreList {
    type Err = &'static str;

    fn from_str(_: &str) -> Result<Self, Self::Err> {
        Err("IgnoreList is not parsable")
    }
}

/// Maps client-supplied options to movefmt's internals, mostly overriding
/// values in a config with values from the command line.
pub trait CliOptions {
    fn apply_to(self, config: &mut Config);
    fn config_path(&self) -> Option<&Path>;
}

/// The edition of the syntax and semntics of code (RFC 2052).
#[config_type]
pub enum Edition {
    #[value = "2015"]
    #[doc_hint = "2015"]
    /// Edition 2015.
    Edition2015,
    #[value = "2018"]
    #[doc_hint = "2018"]
    /// Edition 2018.
    Edition2018,
    #[value = "2021"]
    #[doc_hint = "2021"]
    /// Edition 2021.
    Edition2021,
    #[value = "2024"]
    #[doc_hint = "2024"]
    /// Edition 2024.
    Edition2024,
}

impl Default for Edition {
    fn default() -> Edition {
        Edition::Edition2015
    }
}

/// Controls how movefmt should handle leading pipes on match arms.
#[config_type]
pub enum MatchArmLeadingPipe {
    /// Place leading pipes on all match arms
    Always,
    /// Never emit leading pipes on match arms
    Never,
    /// Preserve any existing leading pipes
    Preserve,
}
