# Cedar Lean CLI

This directory contains a command line interface (CLI) for interacting with the Lean formalization of Cedar. This CLI uses [`Cedar`](https://github.com/cedar-policy/cedar) to parse policies, schemas, entities, and requests and then uses the Lean formalization of Cedar to perform validation, evaluation, authorization, and analysis.

## Build

### Docker Build

The simplest way to build the CLI is to use the provided Dockerfile to build and run the cli within a docker container.

```
# Create a docker image that is identified with the tag "cedar-lean-cli"
cd cedar-lean-cli                                   # Enter the cedar-lean-cli directory
docker build -t cedar-lean-cli -f ./Dockerfile ..

# Create and enter a container using the newly created cedar-lean-cli docker image
docker run -it cedar-lean-cli

# You can now run the cedar-lean-cli within the container
bash-5.2# cedar-lean-cli help
```

If you prefer to install directly on your machine, you may follow the below detailed instructions for installing `cedar-lean-cli` from source.

### Build from source

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

#### Build this CLI

Use the following commands to build `cedar-lean-cli`

```
cd cedar-lean-ffi                                   # Enter the cedar-lean-ffi library directory
source set_env_vars.sh                              # Updates environment variables with Lean's library location
./build_lean_lib.sh                                 # Build the Lean model of Cedar

cd ../cedar-lean-cli                                     # Enter this directory
cargo install --path .                              # Build and install this CLI
```

Consider adding `source <path-to-cedar-spec>/cedar-lean-ffi/set_env_vars.sh` to your `~/.bashrc` or `~/.profile` to ensure Lean's library path is automatically exported in all new terminal sessions.

If you try to run `cedar-lean-cli` and get the error `cedar-lean-cli: error while loading shared libraries: libleanshared.so: cannot open shared object file: No such file or directory` you need to run `source set_env_vars.sh`.

## Usage

This CLI implements 4 high-level commands `analyze`, `evaluate`, `validate`, and `symcc`:

* The `analyze` command gives access to Cedar's Analyzer for analyzing either a single policyset for warnings or comparing one policyset to another.
* The `evaluate` command gives access to Cedar's evaluation to either evaluate a Cedar expression or authorization request.
* The `validate` command gives access to Cedar's validation to validate a policyset, entities, an authorization request, or a set of entities.
* The `symcc` command gives access to Cedar's Symbolic Compiler---a lower level interface to Cedar's analysis capabilities.

```
> cedar-lean-cli --help
Command Line Interface for Cedar Lean

Usage: cedar-lean-cli <COMMAND>

Commands:
  analyze   Run the Cedar Analyzer
  evaluate  Evaluate a Cedar PolicySet or Expression
  validate  Validate PolicySets, Entities, or Requests against a Schema
  symcc    Run the Cedar Symbolic Compiler
  help      Print this message or the help of the given subcommand(s)

Options:
  -h, --help     Print help
  -V, --version  Print version
```

### Analysis

The `analyze` command provides two sub-commands `policies` and `compare`.

* The `policies` command will analyze a single policyset and present a set of findings about each policy within the policyset.
* The `compare` command takes two policysets and determines for each "type" of request if the first policyset is equivalent, less permissive, more permissive, or incomparable to the second policyset (in terms of the requests allowed by each policyset).

```
> cedar-lean-cli analyze --help
Run the Cedar Analyzer

Usage: cedar-lean-cli analyze <COMMAND>

Commands:
  policies  Analyze a PolicySet
  compare   Compare two PolicySets
  help      Print this message or the help of the given subcommand(s)

Options:
  -j, --json-output  Whether to output the compare policy sets output in .json format
  -h, --help  Print help
```

For both sub-commands, the CLI supports both a "human readable output" (default) and a more "machine friendly" JSON format (`--json-output`).

#### Analyze Policies

The `analyze policies` command presents five findings: if a policy is vacuous, if a subset of policies are redundant (i.e., are equivalent to each other), if a permit policy is shadowed by another permit policy, if a permit policy is overrident by forbid policy, or if a fordid policy is shadowed by another forbid policy. We present the findings (other than vacuousness of policies) per request type.

* A policy is vacous if either (1) it applies to all requests (allows all) or (2) it applies to no requests (allows none).
* A set of policies are redundant with each other if every policy within the set are equivalent (allows the same set of authorization requests).
* A permit policy `policy1` is shadowed by a permit policy `policy2` if every request allowed by `policy1` is allowed by `policy2` and `policy1` and `policy2` are not redundant.
* A permit policy `policy1` is overriden by a forbid policy `policy2` if every request allowed by `policy1` is denied by `policy2`.
* A forbid policy `policy1` is shaddowed by a forbid policy `policy2` if every request denied by `policy1` is denied by `policy2` and `policy1` and `policy2` are not redundant.

#### Analyze Compare

The `analyze compare` command compares two policysets (`pset1` and `pset2`) per request "type". For each type, it determines if `pset` is equivalent to `pset2`, if `pset1` is less permissive than `pset2`, if `pset1` is more permissive than `pset2`, or if `pset1` and `pset2` are incomparable.

* `pset1` is equivalent to `pset2`: the set of authorizations allowed by `pset1` and `pset2` are identical
* `pset1` is less permissive than `pset2`: the set of authorization requests allowed by `pset1` is a strict subset of the requests allowed by `pset2`.
* `pset1` is more permissive than `pset2`: the set of authorization requests allowed by `pset1` is a strict superset of the requests allowed by `pset2`.
* `pset1` is incomparable to `pset2`: none of the above options apply. That is, there is some authorization request allowed by `pset1` and not `pset2`, and some other authorization request allowed by `pset2` and not `pset1`.

### Symbolic Compilation

The `symcc` command provides an interface to access Cedar's Symbolic Compiler. The Symbolic compiler provides a lower level interface to Cedar's analysis capabilities. The `symcc` command has six sub-commands `check-never-errors`, `check-always-allows`, `check-always-denies`, `check-equivalent`, `check-implies`, `check-disjoint`.

* `check-never-errors`: Checks if a policy will never throw an error during evaluation.
* `check-always-allows`: Checks if a policy allows all authorization requests.
* `check-always-denies`: Checks if a policy denies all authorization requests.
* `check-equivalent`: Compares two policy sets `pset1` and `pset2`; Checks if `pset1` and `pset2` allow the same set of authorization requests.
* `check-implies`: Compares two policy sets `pset1` and `pset2`; Checks if every authorization request allowed by `pset1` is also allowed by `pset2`.
* `check-disjoint`: Compares two policy sets `pset1` and `pset2`; Checks if `pset1` and `pset2` allow disjoint sets of authorization requests.

```
> cedar-lean-cli symcc --help
Run the Cedar Symbolic Compiler

Usage: cedar-lean-cli symcc <COMMAND>

Commands:
  check-never-errors   Check if the provided Policy never errors
  check-always-allows  Check if the provided PolicySet allows all authorization requests
  check-always-denies  Check if the provided PolicySet denies all authorization requests
  check-equivalent     Check if two PolicySets are equivalent
  check-implies        Check if one PolicySet authorizes all requests that another PolicySet authorizes
  check-disjoint       Check if two PolicySets are disjoint (there is no authorization request that both PolicySets allow)
  help                 Print this message or the help of the given subcommand(s)

Options:
  -h, --help  Print help
```

For each of the six sub-commands, you may either run the analysis (`--run-analysis`) or print out an [SMT-LIB](https://smt-lib.org/) file containing the necessary checks to run the analysis (`--print-smtlib`).

Additionally, for all six sub-commands you may restrict the analyses to a specific principal type, action, or resource type.

```
Execution Modes:
      --run-analysis  Run the SMT formula produced by the provided backend encoder via CVC5 [default]
      --print-smtlib  Print the SMT formula produced by the provided backend

Request Environment Options:
      --principal-type <PRINCIPAL_TYPE_NAME>
          Restrict Analysis to Request Environments for the given PrincipalType
      --action-name <ACTION_NAME>
          Restrict Analysis to Request Environmetns for the given Action
      --resource-type <RESOURCE_TYPE_NAME>
          Restrict Analysis to Request Environments for the given ResourceType
```

### Evaluation

The `evaluate` command provides two sub-commands `authorize` and `evaluate`.
* The `authorize` sub-command evaluates an authorization request.
* The `evaluate` sub-command evalutes a cedar expression (and optionally compares the evaluated expression to a cedar value).

```
> cedar-lean-cli evaluate --help
Evaluate a Cedar PolicySet or Expression

Usage: cedar-lean-cli evaluate <COMMAND>

Commands:
  authorize  Check if a given PolicySet allows or denies a Request
  evaluate   Evaluate a Cedar Expression
  help       Print this message or the help of the given subcommand(s)

Options:
  -h, --help  Print help
```

### Validation

The `validate` command provides four sub-commands `policy-set`, `level`, `request`, and `entities`.
* The `policy-set` sub-command validates a policyset against a given Schema.
* The `level` sub-command validates a policyset against a given Schema at a desired level (maximum reference depth of field identifiers).
* The `request` sub-command validates an authorization request against a given Schema.
* The `entities` sub-command validates a set of entities against a given Schema.

```
> cedar-lean-cli validate --help
Validate PolicySets, Entities, or Requests against a Schema

Usage: cedar-lean-cli validate <COMMAND>

Commands:
  policy-set  Validate a PolicySet against a Schema
  level       Validate a PolicySet against a Schema using level-based validation
  request     Validate a Request against a Schema
  entities    Validate Entities against a Schema
  help        Print this message or the help of the given subcommand(s)

Options:
  -h, --help  Print help
```
