# Cedar Specification

This repository contains the Dafny formalization of Cedar and infrastructure for performing differential randomized testing (DRT) between the formalization and Rust production implementation available in [cedar](https://github.com/cedar-policy/cedar).

## Repository Structure

* [`cedar-lean`](./cedar-lean) contains the Lean formalization of, and proofs about, Cedar.
* [`cedar-dafny`](./cedar-dafny) contains the Dafny formalization of, and proofs about, Cedar.
* [`cedar-dafny-java-wrapper`](./cedar-dafny-java-wrapper) contains the Java interface for DRT.
* [`cedar-drt`](./cedar-drt) contains code for fuzzing, property-based testing, and differential testing of Cedar.
* [`cedar-policy-generators`](./cedar-policy-generators) contains code for generating schemas, entities, policies, and requests using the [arbitrary](https://docs.rs/arbitrary/latest/arbitrary/index.html#) crate.
* `cedar` is a git submodule, pinned to the associated commit of [cedar](https://github.com/cedar-policy/cedar).

## Build

To build the Dafny formalization and proofs:

* Install Dafny, following the instructions [here](https://github.com/dafny-lang/dafny/wiki/INSTALL). Our proofs expect Z3 version 4.12.1, so if you have another copy of Z3 installed locally, you may need to adjust your PATH.
* `cd cedar-dafny && make verify test`

To build the Lean formalization and proofs:

* Install Lean, following the instructions [here](https://leanprover.github.io/lean4/doc/setup.html).
* `cd cedar-lean && lake build Cedar`

To build the DRT framework:

* Install Dafny and Lean, following the instructions above.
* `./build.sh`

Note that the build for DRT has only been tested on **Amazon Linux 2**.

## Run

To run DRT:

* `cd cedar-drt && source ./set_env_vars.sh`
* `cargo fuzz run -s none <target> -j8` (choose an appropriate -j for your machine).

List the available fuzz targets with `cargo fuzz list`.
Available targets are described in the README in the `cedar-drt` directory.

Additional commands available with `cargo fuzz help`.

## Checking Proof Stability

You can measure the complexity of Dafny proofs using [dafny-reportgenerator](https://github.com/dafny-lang/dafny-reportgenerator/).
For example, the commands below check that all proofs have a [resource count](https://dafny.org/dafny/VerificationOptimization/VerificationOptimization#identifying-difficult-assertions) under 10M, which is our informal threshold for when a proof is "too expensive" and likely to break with future changes to Dafny and/or Z3.

```bash
cd cedar-dafny && make verify GEN_STATS=1
dotnet tool run dafny-reportgenerator summarize-csv-results --max-resource-count 10000000 .
```

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
