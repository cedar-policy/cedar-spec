# Cedar Specification

This repository contains the formalization of Cedar and infrastructure for performing differential randomized testing (DRT) between the formalization and Rust production implementation available in [`cedar`](https://github.com/cedar-policy/cedar).

You can learn more about our formalization efforts in the following blog posts:

* [How we built Cedar with automated reasoning and differential testing](https://www.amazon.science/blog/how-we-built-cedar-with-automated-reasoning-and-differential-testing)
* [Lean Into Verified Software Development](https://aws.amazon.com/blogs/opensource/lean-into-verified-software-development/)

## Repository Structure

* [`cedar-lean`](./cedar-lean) contains the Lean formalization of, and proofs about, Cedar.
* [`cedar-drt`](./cedar-drt) contains code for fuzzing, property-based testing, and differential testing of Cedar.
* [`cedar-policy-generators`](./cedar-policy-generators) contains code for generating schemas, entities, policies, and requests using the [arbitrary](https://docs.rs/arbitrary/latest/arbitrary/index.html#) crate.

See the README in each directory for more information.

## Build

### Lean formalization and proofs

* Install Lean, following the instructions [here](https://leanprover.github.io/lean4/doc/setup.html).
* `cd cedar-lean`
* `source ../cedar-drt/set_env_vars.sh`
* `lake build Cedar`

### DRT framework

The simplest way to build our DRT framework is to use the included Dockerfile:

```bash
docker build . -t cedar_drt # ~10 minutes
docker run --rm -it cedar_drt
```

If you'd rather not use Docker, here are the full instructions for a local build:

* Install Lean, following the instructions above.
* Clone the `cedar` repository in the current (`cedar-spec`) repository.
* `source cedar-drt/set_env_vars.sh`
* `cd cedar-lean && lake build Cedar:static DiffTest:static Batteries:static`
* `cd ../cedar-drt && cargo build`

The build has only been tested on **Amazon Linux 2**.

## Run

To run DRT:

* Follow the build instructions above.
* If running locally, `source ./set_env_vars.sh`.
* `cargo fuzz run -s none <target>`.

List the available fuzz targets with `cargo fuzz list`.
Available targets are described in the README in the `cedar-drt` directory.
That README also explains how to debug build failures, and how to save DRT-generated tests.

Additional commands available with `cargo fuzz help`.

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
