# cedar-spec

You can just build `cedar-dafny` or you can build everything in this repository.


For exact build instructions, we recommend looking at `.github/workflows/ci.yml`


TLDR;
- Install Dafny and Z3 (ensure Z3 is on your path)
- `cd cedar-dafny && make`

If you want to run the fuzzer:

- To build the definitional engine:
- Set JAVA_HOME
- Set LD_LIBRARY_PATH to include `$JAVA_HOME/lib/server`
- `cd cedar-dafny && make compile-difftest`

To build `cedar-dafny-java-wrapper` (you must have run `make compile-difftest` above first)
- `cd cedar-dafny-java-wrapper && ./gradlew build dumpClasspath`

To compile `cedar-drt`
- Clone [cedar](https://github.com/cedar-policy/cedar) to `cedar-spec/cedar`
- Ensure `JAVA_HOME` and `LD_LIBRARY_PATH` are set as above
- `export CLASSPATH="$(< ../cedar-dafny-java-wrapper/build/runtimeClasspath.txt):$(pwd)/../cedar-dafny-java-wrapper/build/libs/cedar-dafny-java-wrapper.jar"`
- `cd cedar-drt && cargo build`
- `cargo test`
- `cd fuzz && RUSTFLAGS="--cfg=fuzzing" cargo build`
Change the arguments to `cargo fuzz run` as desired. E.g.,
`cd cedar-drt && source ./set_env_vars.sh && cargo fuzz run -s none abac-type-directed`


## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.

