# Cedar Specification

This repository contains the Dafny formalization of Cedar and infrastructure for performing differential randomized testing (DRT) between the formalization and Rust production implementation available in [cedar](https://github.com/cedar-policy/cedar).

## Repository Structure

* `cedar-spec` contains the Dafny formalization of, and proofs about, Cedar.
* `cedar-dafny-java-wrapper` contains the Java interface for DRT.
* `cedar-drt` contains code for input generation, fuzzing, property-based testing, and differential testing of Cedar.

## Build

To build the Dafny formalization and proofs:

* Install Dafny and Z3 version 4.12.1, following the instructions [here](https://github.com/dafny-lang/dafny/wiki/INSTALL). Ensure that Z3 is on your path.
* `cd cedar-dafny && make`

To build the DRT framework:

* Set JAVA_HOME
* Set LD_LIBRARY_PATH to include `$JAVA_HOME/lib/server`
* Clone [cedar](https://github.com/cedar-policy/cedar) to `cedar-spec/cedar`
* `./build.sh`

## Run

To run DRT:

* `cd cedar-drt && source ./set_env_vars.sh`
* `cargo fuzz run -s none <target> -j8` (choose an appropriate -j for your machine).

List the available fuzz targets with `cargo fuzz list`.
Available targets are described in the README in the `cedar-drt` directory.

Additional commands available with `cargo fuzz help`.

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
