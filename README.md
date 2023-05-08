# Cedar Spec

This repository contains the Dafny formalization of Cedar and infrastructure for performing differential testing between the formalization and Rust production engine (available in [cedar](https://github.com/cedar-policy/cedar)).

## Build

For exact build instructions, we recommend looking at `.github/workflows/ci.yml`

### `cedar-dafny`

Basic build for the formalization and proofs:

- Install Dafny and Z3 (ensure Z3 is on your path)
- `cd cedar-dafny && make`

If you want to run differential testing:

- To build the definitional engine:
- Set JAVA_HOME
- Set LD_LIBRARY_PATH to include `$JAVA_HOME/lib/server`
- `cd cedar-dafny && make compile-difftest`
- `cd cedar-dafny-java-wrapper && ./gradlew build dumpClasspath`

### `cedar-drt`

- Clone [cedar](https://github.com/cedar-policy/cedar) to `cedar-spec/cedar`
- Ensure `JAVA_HOME` and `LD_LIBRARY_PATH` are set as above
- `export CLASSPATH="$(< ../cedar-dafny-java-wrapper/build/runtimeClasspath.txt):$(pwd)/../cedar-dafny-java-wrapper/build/libs/cedar-dafny-java-wrapper.jar"`
- `cd cedar-drt && cargo build`
- `cargo test`
- `cd fuzz && RUSTFLAGS="--cfg=fuzzing" cargo build`

## Run

Change to the `cedar-drt` directory and source `./set_env_vars.sh`:

```[bash]
cd cedar-drt && source ./set_env_vars.sh
```

List the available fuzz targets with `cargo fuzz list`.
Some of these do pure fuzzing, others property-based testing, others differential testing, or some combination of these.
Available targets are described in the README in the `cedar-drt` directory.

Run a target with `cargo fuzz run -s none <target> -j8` (choose an appropriate -j for your machine).

More commands available with `cargo fuzz help`.

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
