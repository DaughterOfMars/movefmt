use anyhow::{format_err, Result};
use io::Error as IoError;
use thiserror::Error;
use tracing_subscriber::EnvFilter;
use std::env;
use std::fs::File;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use getopts::{Matches, Options};
use movefmt::{
    core::fmt::FormatConfig,
    syntax::parse_file_string,
};
use commentfmt::{load_config, Config, CliOptions, Verbosity, EmitMode};
use move_command_line_common::files::FileHash;
use move_compiler::{shared::CompilationEnv, Flags};
use std::collections::BTreeSet;

fn main() {
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_env("MOVEFMT_LOG"))
        .init();
    let opts = make_opts();

    let exit_code = match execute(&opts) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("{e:#}");
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
    Format {
        files: Vec<PathBuf>,
    },
    /// Print the help message.
    Help(HelpOp),
    /// Print version information
    Version,
    /// Output default config to a file, or stdout if None
    ConfigOutputDefault { path: Option<String> },
    /// Output current config (as if formatting to a file) to stdout
    ConfigOutputCurrent { path: Option<String> },
    /// No file specified, read from stdin
    Stdin { input: String },
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
        "Dumps a default or current config to PATH(eg: movefmt.config)",
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

            let (config, _) = load_config(Some(file.parent().unwrap()), Some(options))?;
            let toml = config.all_options().to_toml()?;
            io::stdout().write_all(toml.as_bytes())?;

            Ok(0)
        }
        Operation::Stdin { input } => format_string(input, options),
        Operation::Format {
            files,
        } => format(files, &options),
    }
}

fn format_string(input: String, options: GetOptsOptions) -> Result<i32> {
    println!("input = {}, options = {:?}", input, options);
    let output =
        movefmt::core::fmt::format(input, FormatConfig { indent_size: 4 }).unwrap();
    println!("output = {}", output);
    Ok(0)
}

fn format(
    files: Vec<PathBuf>,
    options: &GetOptsOptions,
) -> Result<i32> {
    println!("files = {:?}, options = {:?}", files, options);
    for file in files {
        let content_origin = std::fs::read_to_string(&file.as_path()).unwrap();
        let attrs: BTreeSet<String> = BTreeSet::new();
        let mut env = CompilationEnv::new(Flags::testing(), attrs);
        match parse_file_string(&mut env, FileHash::empty(), &content_origin) {
            Ok(_) => {
                let formatted_text =
                    movefmt::core::fmt::format(content_origin, FormatConfig { indent_size: 4 }).unwrap();
                std::fs::write(file, formatted_text)?;
            }
            Err(_) => {
                eprintln!("file '{:?}' skipped because of parse not ok", file);
            }
        }
    }
    Ok(0)
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
    println!("movefmt v0.0.1");
}

fn determine_operation(matches: &Matches) -> Result<Operation, OperationError> {
    if matches.opt_present("h") {
        let topic = matches.opt_str("h");
        if topic == None {
            return Ok(Operation::Help(HelpOp::None));
        } else if topic == Some("config".to_owned()) {
            return Ok(Operation::Help(HelpOp::Config));
        } else {
            return Err(OperationError::UnknownHelpTopic(topic.unwrap()));
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

    // if no file argument is supplied, read from stdin
    if files.is_empty() {
        let mut buffer = String::new();
        io::stdin().read_to_string(&mut buffer)?;
        return Ok(Operation::Stdin { input: buffer });
    }

    Ok(Operation::Format {
        files
    })
}

// const STABLE_EMIT_MODES: [EmitMode; 3] = [EmitMode::Files, EmitMode::Stdout, EmitMode::Diff];

/// Parsed command line options.
#[derive(Clone, Debug, Default)]
struct GetOptsOptions {
    quiet: bool,
    verbose: bool,
    config_path: Option<PathBuf>,
    emit_mode: Option<EmitMode>,
}

impl GetOptsOptions {
    pub fn from_matches(matches: &Matches) -> Result<GetOptsOptions> {
        let mut options = GetOptsOptions::default();
        options.verbose = matches.opt_present("verbose");
        options.quiet = matches.opt_present("quiet");
        if options.verbose && options.quiet {
            return Err(format_err!("Can't use both `--verbose` and `--quiet`"));
        }

        options.config_path = matches.opt_str("config-path").map(PathBuf::from);
        if let Some(ref emit_str) = matches.opt_str("emit") {
            options.emit_mode = Some(emit_mode_from_emit_str(emit_str)?);
        }
        Ok(options)
    }
}

impl CliOptions for GetOptsOptions {
    fn apply_to(self, config: &mut Config) {
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
    }

    fn config_path(&self) -> Option<&Path> {
        self.config_path.as_deref()
    }
}

fn emit_mode_from_emit_str(emit_str: &str) -> Result<EmitMode> {
    match emit_str {
        "files" => Ok(EmitMode::Files),
        "new_files" => Ok(EmitMode::NewFiles),
        "stdout" => Ok(EmitMode::Stdout),
        _ => Err(format_err!("Invalid value for `--emit`")),
    }
}
