// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// Copyright © Aptos Foundation
// Copyright (c) The BitsLab.MoveBit Contributors
// SPDX-License-Identifier: Apache-2.0

use std::{
    collections::HashMap,
    path::{Path, PathBuf},
};

use commentfmt::{load_config, CliOptions, Config, EmitMode, Verbosity};
use getopts::Matches;
use move_compiler::diagnostics::Diagnostics;

pub use self::tools::movefmt_diff::diff;
use crate::{
    core::fmt::format_entry,
    tools::{
        movefmt_diff::{print_mismatches_default_message, DIFF_CONTEXT_SIZE},
        utils::mk_result_filepath,
    },
};

#[macro_export]
macro_rules! impl_convert_loc {
    ($struct_name : ident) => {
        impl ConvertLoc for $struct_name {
            fn convert_file_hash_filepath(&self, hash: &FileHash) -> Option<PathBuf> {
                self.hash_file.as_ref().borrow().get_path(hash).map(|x| x.clone())
            }
            fn convert_loc_range(&self, loc: &Loc) -> Option<FileRange> {
                self.convert_file_hash_filepath(&loc.file_hash())
                    .map(|file| {
                        self.file_line_mapping
                            .as_ref()
                            .borrow()
                            .translate(&file, loc.start(), loc.end())
                    })
                    .flatten()
            }
        }
    };
}

pub mod core;
pub mod syntax_fmt;
pub mod tools;

#[derive(Debug, thiserror::Error)]
pub enum FormatError {
    #[error("Can't use both `--verbose` and `--quiet`")]
    VerboseAndQuiet,
    #[error("Invalid value for `--emit`")]
    InvalidEmit,
    #[error("invalid key-value pair: `{key}={val}`")]
    InvalidKeyValuePair { key: String, val: String },
    #[error("{0:#?}")]
    Diagnostics(Diagnostics),
    #[error(transparent)]
    IO(#[from] std::io::Error),
}

/// Parsed command line options.
#[derive(Clone, Debug, Default)]
pub struct GetOptsOptions {
    quiet: bool,
    verbose: bool,
    config_path: Option<PathBuf>,
    emit_mode: Option<EmitMode>,
    inline_config: HashMap<String, String>,
}

impl GetOptsOptions {
    pub fn from_matches(matches: &Matches) -> Result<GetOptsOptions, FormatError> {
        let mut options = GetOptsOptions {
            verbose: matches.opt_present("verbose"),
            quiet: matches.opt_present("quiet"),
            ..Default::default()
        };
        if options.verbose && options.quiet {
            return Err(FormatError::VerboseAndQuiet);
        }

        options.config_path = matches.opt_str("config-path").map(PathBuf::from);
        if let Some(ref emit_str) = matches.opt_str("emit") {
            options.emit_mode = Some(emit_mode_from_emit_str(emit_str)?);
        }
        options.inline_config = matches
            .opt_strs("config")
            .iter()
            .flat_map(|config| config.split(','))
            .map(|key_val| match key_val.char_indices().find(|(_, ch)| *ch == '=') {
                Some((middle, _)) => {
                    let (key, val) = (&key_val[..middle], &key_val[middle + 1..]);
                    if !Config::is_valid_key_val(key, val) {
                        Err(FormatError::InvalidKeyValuePair {
                            key: key.to_owned(),
                            val: val.to_owned(),
                        })
                    } else {
                        Ok((key.to_string(), val.to_string()))
                    }
                }

                None => Err(FormatError::InvalidKeyValuePair {
                    key: key_val.to_owned(),
                    val: Default::default(),
                }),
            })
            .collect::<Result<HashMap<_, _>, _>>()?;

        Ok(options)
    }
}

pub fn format_text(content: &str, options: &GetOptsOptions) -> Result<String, FormatError> {
    tracing::debug!("[format_text] options = {:?}", options);
    let (config, config_path) = load_config(None, Some(options))?;
    tracing::info!(
        "config.[verbose, indent] = [{:?}, {:?}], {:?}",
        config.verbose(),
        config.indent_size(),
        options
    );

    if config.verbose() == Verbosity::Verbose {
        if let Some(path) = config_path.as_ref() {
            println!("Using movefmt config file {}", path.display());
        }
    }

    Ok(format_entry(&content, &config).map_err(|d| FormatError::Diagnostics(d))?)
}

pub fn format_files(files: Vec<PathBuf>, options: &GetOptsOptions) -> Result<(), FormatError> {
    tracing::debug!("[format_files] options = {:?}", options);
    let (mut config, config_path) = load_config(None, Some(options))?;
    tracing::info!(
        "config.[verbose, indent] = [{:?}, {:?}], {:?}",
        config.verbose(),
        config.indent_size(),
        options
    );

    if config.verbose() == Verbosity::Verbose {
        if let Some(path) = config_path.as_ref() {
            println!("Using movefmt config file {}", path.display());
        }
    }

    for file in files {
        if !file.exists() {
            eprintln!("Error: file `{}` does not exist", file.to_str().unwrap());
            continue;
        } else if file.is_dir() {
            eprintln!("Error: `{}` is a directory", file.to_str().unwrap());
            continue;
        } else {
            // Check the file directory if the config-path could not be read or not provided
            if let Some(config_path) = &config_path {
                if config.verbose() == Verbosity::Verbose {
                    println!(
                        "Using movefmt config file {} for {}",
                        config_path.display(),
                        file.display()
                    );
                }
            } else {
                let (local_config, config_path) = load_config(Some(file.parent().unwrap()), Some(options))?;
                tracing::debug!("local config_path = {:?}", config_path);
                if let Some(path) = config_path {
                    if local_config.verbose() == Verbosity::Verbose {
                        println!(
                            "Using movefmt local config file {} for {}",
                            path.display(),
                            file.display()
                        );
                    }
                    config = local_config;
                }
            }
        }

        let original_text = std::fs::read_to_string(file.as_path()).unwrap();
        let formatted_text = format_entry(&original_text, &config).map_err(|d| FormatError::Diagnostics(d))?;
        let emit_mode = if let Some(op_emit) = options.emit_mode {
            op_emit
        } else {
            config.emit_mode()
        };
        match emit_mode {
            EmitMode::NewFiles => std::fs::write(mk_result_filepath(&file.to_path_buf()), formatted_text)?,
            EmitMode::Files => {
                std::fs::write(&file, formatted_text)?;
            }
            EmitMode::Stdout => {
                println!("{}", formatted_text);
            }
            EmitMode::Diff => {
                let compare = diff(&formatted_text, &original_text, DIFF_CONTEXT_SIZE);
                if !compare.is_empty() {
                    let mut failures = HashMap::new();
                    failures.insert(file.to_owned(), compare);
                    print_mismatches_default_message(failures);
                }
            }
        }
    }
    Ok(())
}

fn emit_mode_from_emit_str(emit_str: &str) -> Result<EmitMode, FormatError> {
    Ok(match emit_str {
        "files" => EmitMode::Files,
        "new_files" => EmitMode::NewFiles,
        "stdout" => EmitMode::Stdout,
        "check_diff" => EmitMode::Diff,
        _ => return Err(FormatError::InvalidEmit),
    })
}

impl CliOptions for GetOptsOptions {
    fn apply_to(&self, config: &mut Config) {
        if self.verbose {
            config.set().verbose(Verbosity::Verbose);
        } else if self.quiet {
            config.set().verbose(Verbosity::Quiet);
        } else {
            config.set().verbose(Verbosity::Normal);
        }
        if let Some(emit_mode) = self.emit_mode {
            config.set().emit_mode(emit_mode);
        }
        for (key, val) in &self.inline_config {
            config.override_value(key, val);
        }
    }

    fn config_path(&self) -> Option<&Path> {
        self.config_path.as_deref()
    }
}
