// Copyright © Aptos Foundation
// Copyright (c) The BitsLab.MoveBit Contributors
// SPDX-License-Identifier: Apache-2.0

use std::{
    env,
    fs::File,
    io::{self, Write},
    path::PathBuf,
};

use anyhow::{format_err, Result};
use commentfmt::{load_config, Config};
use getopts::{Matches, Options};
use io::Error as IoError;
use movefmt::{format_files, GetOptsOptions};
use thiserror::Error;
use tracing_subscriber::EnvFilter;

fn main() {
    dotenvy::dotenv().ok();
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_env("MOVEFMT_LOG"))
        .init();
    let opts = make_opts();

    let exit_code = match execute(&opts) {
        Ok(code) => code,
        Err(e) => {
            tracing::info!("{e:#}");
            1
        }
    };
    // Make sure standard output is flushed before we exit.
    std::io::stdout().flush().unwrap();

    // Exit with given exit code.
    //
    // NOTE: this immediately terminates the process without doing any cleanup,
    // so make sure to finish all necessary cleanup before this is called.
    std::process::exit(exit_code);
}

/// movefmt operations.
enum Operation {
    /// Format files and their child modules.
    Format { files: Vec<PathBuf> },
    /// Print the help message.
    Help(HelpOp),
    /// Print version information
    Version,
    /// Output default config to a file, or stdout if None
    ConfigOutputDefault { path: Option<String> },
    /// Output current config (as if formatting to a file) to stdout
    ConfigOutputCurrent { path: Option<String> },
}

/// movefmt operations errors.
#[derive(Error, Debug)]
pub enum OperationError {
    /// An unknown help topic was requested.
    #[error("Unknown help topic: `{0}`.")]
    UnknownHelpTopic(String),
    /// An unknown print-config option was requested.
    #[error("Unknown print-config option: `{0}`.")]
    UnknownPrintConfigTopic(String),
    /// An io error during reading or writing.
    #[error("{0}")]
    IoError(IoError),
}

impl From<IoError> for OperationError {
    fn from(e: IoError) -> OperationError {
        OperationError::IoError(e)
    }
}

/// Arguments to `--help`
enum HelpOp {
    None,
    Config,
}

fn make_opts() -> Options {
    let mut opts = Options::new();
    let emit_opts = "[files|new_files|stdout|check_diff]";

    opts.optopt("", "emit", "What data to emit and how", emit_opts);
    opts.optopt(
        "",
        "config-path",
        "Recursively searches the given path for the movefmt.toml config file",
        "[Path for the configuration file]",
    );
    opts.optopt(
        "",
        "print-config",
        "Dumps a default or current config to PATH(eg: movefmt.toml)",
        "[default|current] PATH",
    );
    opts.optmulti(
        "",
        "config",
        "Set options from command line. These settings take priority over .movefmt.toml",
        "[key1=val1,key2=val2...]",
    );

    opts.optflag("v", "verbose", "Print verbose output");
    opts.optflag("q", "quiet", "Print less output");
    opts.optflag("V", "version", "Show version information");
    let help_topic_msg = "Show help".to_owned();
    opts.optflagopt("h", "help", &help_topic_msg, "=TOPIC");

    opts
}

// Returned i32 is an exit code
fn execute(opts: &Options) -> Result<i32> {
    let matches = opts.parse(env::args().skip(1))?;
    let options = GetOptsOptions::from_matches(&matches)?;

    match determine_operation(&matches)? {
        Operation::Help(HelpOp::None) => {
            print_usage_to_stdout(opts, "");
            Ok(0)
        }
        Operation::Help(HelpOp::Config) => {
            print_usage_to_stdout(opts, "");
            Ok(0)
        }
        Operation::Version => {
            print_version();
            Ok(0)
        }
        Operation::ConfigOutputDefault { path } => {
            let toml = Config::default().all_options().to_toml()?;
            if let Some(path) = path {
                let mut file = File::create(path)?;
                file.write_all(toml.as_bytes())?;
            } else {
                io::stdout().write_all(toml.as_bytes())?;
            }
            Ok(0)
        }
        Operation::ConfigOutputCurrent { path } => {
            let path = match path {
                Some(path) => path,
                None => return Err(format_err!("PATH required for `--print-config current`")),
            };

            let file = PathBuf::from(path);
            let file = file.canonicalize().unwrap_or(file);

            let (config, _) = load_config(Some(file.parent().unwrap()), Some(&options))?;
            let toml = config.all_options().to_toml()?;
            io::stdout().write_all(toml.as_bytes())?;

            Ok(0)
        }
        Operation::Format { files } => {
            format_files(files, &options)?;
            Ok(0)
        }
    }
}

fn print_usage_to_stdout(opts: &Options, reason: &str) {
    let sep = if reason.is_empty() {
        String::new()
    } else {
        format!("{reason}\n\n")
    };
    let msg = format!("{sep}Format Move code\n\nusage: movefmt [options] <file>...");
    println!("{}", opts.usage(&msg));
}

fn print_version() {
    println!("movefmt v1.0.0");
}

fn determine_operation(matches: &Matches) -> Result<Operation, OperationError> {
    if matches.opt_present("h") {
        let topic = matches.opt_str("h");
        if topic.is_none() {
            return Ok(Operation::Help(HelpOp::None));
        } else if topic == Some("config".to_owned()) {
            return Ok(Operation::Help(HelpOp::Config));
        }
    }
    let mut free_matches = matches.free.iter();
    if let Some(kind) = matches.opt_str("print-config") {
        let path = free_matches.next().cloned();
        match kind.as_str() {
            "default" => return Ok(Operation::ConfigOutputDefault { path }),
            "current" => return Ok(Operation::ConfigOutputCurrent { path }),
            _ => {
                return Err(OperationError::UnknownPrintConfigTopic(kind));
            }
        }
    }

    if matches.opt_present("version") {
        return Ok(Operation::Version);
    }

    let files: Vec<_> = free_matches
        .map(|s| {
            let p = PathBuf::from(s);
            // we will do comparison later, so here tries to canonicalize first
            // to get the expected behavior.
            p.canonicalize().unwrap_or(p)
        })
        .collect();

    if files.is_empty() {
        eprintln!("no file argument is supplied \n-------------------------------------\n");
        return Ok(Operation::Help(HelpOp::None));
    }

    Ok(Operation::Format { files })
}
