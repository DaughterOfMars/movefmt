`movefmt` is a code formatting tool for Move on Aptos.

## About Us
MoveBit is a security audit company for the Move ecosystem, with a vision to make the Move ecosystem the most secure Web3. 

The MoveBit team consists of security leaders in academia and enterprise world, with 10 years of security experience, and is the first blockchain security company to leverage formal verification in the Move ecosystem.

## Background
An automated formatting tool makes code look uniform and pretty (in an opinionated way). A programmer can then focus on the logic of the program instead of formatting-related minutiae.

There was a marked absence of a developer-friendly formatting tool in the move ecosystem. MoveBit has now filled this gap by developing `movefmt`.

## Install

Run the following command to install `movefmt`.

```
$ cargo install --git https://github.com/movebit/movefmt --branch develop movefmt
```

On MacOS and Linux, `movefmt` is typically installed in directory `~/.cargo/bin`.
Ensure to have this path in your `PATH` environment variable so `movefmt` can be executed from any location.
This step can be done with the below command.

```
$ export PATH=~/.cargo/bin:$PATH
```

You can also use the latest pre-built binaries appropriate for your OS from [releases](https://github.com/movebit/movefmt/releases) instead of installing it via `cargo`.

## Build

Follow this step if you instead want to clone and build the tool from source. `movefmt` requires Rust compiler to build. From the root directory, execute the following command.

```
$ git clone https://github.com/movebit/movefmt.git
$ cd movefmt
$ git checkout develop
$ cargo build
```

The resulting binary `movefmt` can be found under the directory `target/debug`.

## Usage
If you wish to use this tool independently.
```
# optionally, set env variable to see the log
export MOVEFMT_LOG=movefmt=DEBUG

# get help msg
movefmt -h

# format source file with printing verbose msg
movefmt -v /path/to/your/file_name.move
```
More detailed usage information is provided here:
> https://github.com/movebit/movefmt/blob/develop/doc/how_to_use.md

Alternatively, you can use the VS Code plugin `aptos-move-analyzer` by installing it. We have integrated `movefmt` into it, which allows you to format the current move file with just one right-click. The VS Code plugin `aptos-move-analyzer` can installed on the plugin market place with detailed guidance.
> https://marketplace.visualstudio.com/items?itemName=MoveBit.aptos-move-analyzer

To use the tool directly with debug logs run `MOVEFMT_LOG=DEBUG cargo run {your_file_name}.move --emit files`.

## Reporting Issues

If you find any problems in using the tool, please feel free to open an issue.

## License

`movefmt` is released under the open source [Apache License](LICENSE)
