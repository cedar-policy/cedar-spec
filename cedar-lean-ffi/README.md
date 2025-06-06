# Cedar Lean FFI (Rust Bindings of Cedar Lean Formalization)

This directory contains Rust bindings for interacting with the Lean formalization of Cedar. This FFI assumes all inputs for `Policy`s, `PolicySet`s, `Entities`, `Schema`s, `Request`s are represented using [`Cedar`](https://github.com/cedar-policy/cedar) public API types. This FFI makes use of Cedar's Protobuf feature to convert Cedar types in Rust to the corresponding type within the Lean formalization.

## Build

### Prerequisites:

#### Install Lean
For more details read about Lean's version manager [elan](https://github.com/leanprover/elan).

```
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

#### Install cvc5 (>= v1.0.5)
The analysis features provided by this CLI requires a local install of [cvc5](https://github.com/cvc5/cvc5) with version [1.0.5](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.0.5) or greater.

Once you install cvc5. Export the following Environment variable which allows this CLI to know where cvc5 is installed. Consider adding the export to your `~/.bashrc` or `~/.profile` so that the environment variable is exported to all new terminal sessions.

```
export CVC5=<PATH-TO-CVC5-EXECUTABLE>
```

#### Install Rust

This CLI is written in Rust and uses Lean's foreign function interface to call the relevant parts of the Cedar lean formalization.

```
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

#### Install Protoc

This CLI uses Protobuf for serializing Cedar data structures between the Rust frontend and Lean backend of this CLI.

Download and install Protobuf. The code has been tested with [Protobuf v29.3](https://github.com/protocolbuffers/protobuf/releases/tag/v29.3). If you are using Linux (on x86_64 arch) and wish to install protobuf to `/usr/local/` you can use the following instructions to install protobuf. For more information see the official [Protobuf installation page](https://github.com/protocolbuffers/protobuf#protobuf-compiler-installation).

```
curl -OL https://github.com/protocolbuffers/protobuf/releases/download/v29.3/protoc-29.3-linux-x86_64.zip
unzip protoc-29.3-linux-x86_64.zip
cp bin/protoc /usr/local/bin/
cp -r include/google/ /usr/local/include/
```

### Build this Library

Use the following commands to build the `cedar-lean-ffi` Library.

```
cd cedar-spec/cedar-lean-ffi        # Enter this directory
source set_env_vars.sh              # Update environment variabels with Lean's library location
./build_lean_lib.sh                 # Build the Lean model of Cedar
cargo build                         # Build this library
```

Consider adding `source source <path-to-cedar-spec>/cedar-lean-ffi/set_env_vars.sh` to your `~/.bashrc` or `~/.profile` to ensure Lean's library path is automatically exported in all new terminal sessions.

If you try to run an executable linked with this library and get the error `error while loading shared libraries: libleanshared.so: cannot open shared object file: No such file or directory` you need to run `source set_env_vars.sh`.
