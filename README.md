# cedar-spec

To use this repository:

1. Download the cedar repository (TODO: add link) and make it a sibling of
this `cedar-spec` repository.

2. Build `cedar-spec` as follows:

```
# Put the correct Z3 on $PATH first. Add -j as desired for a parallel build.
(cd cedar-dafny && make)

(cd cedar-dafny-java-wrapper && ./gradlew build dumpClasspath)

# Change the arguments to `cargo fuzz run` as desired.
(cd cedar-drt && source ./set_env_vars.sh && cargo fuzz run -s none abac-type-directed)
```

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.

