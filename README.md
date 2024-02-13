# Cedar Specification

This repository contains the formalization of Cedar and infrastructure for performing differential randomized testing (DRT) between the formalization and Rust production implementation available in [cedar](https://github.com/cedar-policy/cedar).

## Repository Structure

* [`cedar-lean`](./cedar-lean) contains the Lean formalization of, and proofs about, Cedar.
* [`cedar-drt`](./cedar-drt) contains code for fuzzing, property-based testing, and differential testing of Cedar.
* [`cedar-policy-generators`](./cedar-policy-generators) contains code for generating schemas, entities, policies, and requests using the [arbitrary](https://docs.rs/arbitrary/latest/arbitrary/index.html#) crate.
* `cedar` is a git submodule, pinned to the associated commit of [cedar](https://github.com/cedar-policy/cedar).

## Build

To build the Lean formalization and proofs:

* Install Lean, following the instructions [here](https://leanprover.github.io/lean4/doc/setup.html).
* `cd cedar-lean && lake build Cedar`

To build the DRT framework:

* Install Lean, following the instructions above.
* `./build.sh`

Note that the build for DRT has only been tested on **Amazon Linux 2**.

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
