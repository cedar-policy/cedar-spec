# Cedar Lean

This folder contains the Lean formalization of, and proofs about, Cedar.

## Setup

Follow [these instructions](https://leanprover.github.io/lean4/doc/setup.html) to set up Lean and install the VS Code plugin.

## Usage

To use VS Code, open the `cedar-lean` folder as the root directory.

To build code and proofs from the command line:

```shell
cd cedar-lean
lake exe cache get # gets pre-built libraries for `mathlib4`
lake build Cedar
```

To run the unit tests:

```shell
lake exe CedarUnitTests
```

To run the CLI, use `lake exe Cli`. We provide some example inputs in `Cli/json-inputs`. The authorization examples should all return "allow" and the validation examples should return "ok".

```shell
lake exe Cli authorize Cli/json-inputs/authorize/example2a.json
lake exe Cli validate Cli/json-inputs/validate/example2a.json
```

## Updating the Lean toolchain

Cedar depends on [`mathlib4`](https://github.com/leanprover-community/mathlib4), and it is configured to use the same version of Lean as `mathlib4`.

Follow [these instructions](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency#updating-mathlib4) to update to the latest version of `mathlib4` and Lean:

```shell
curl https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
lake update
lake exe cache get
```

## Contributing

To [contribute](../CONTRIBUTING.md) Lean code or proofs, follow these [style guidelines](GUIDE.md).

## Key definitions

Definitional engine ([`Cedar/Spec/`](Cedar/Spec/))

* [`evaluate`](Cedar/Spec/Evaluator.lean#L76) returns the result of evaluating an expression.
* [`satisfied`](Cedar/Spec/Authorizer.lean#L27) checks if a policy is satisfied for a given request and entities.
* [`isAuthorized`](Cedar/Spec/Authorizer.lean#L38) checks if a request is allowed or denied for a given policy store and entities.

Definitional validator ([`Cedar/Validation/`](Cedar/Validation/))

* [`typeOf`](Cedar/Validation/Typechecker.lean#L235) returns the result of type checking an expression against a schema.

## Verified properties

Basic theorems ([`Cedar/Thm/Basic.lean`](Cedar/Thm/Basic.lean))

* If some forbid policy is satisfied, then the request is denied.
* A request is allowed only if it is explicitly permitted (i.e., there is at least one permit policy that is satisfied).
* If not explicitly permitted, a request is denied.
* Authorization produces the same result regardless of policy evaluation order or duplicates.

Sound policy slicing ([`Cedar/Thm/Slicing.lean`](Cedar/Thm/Slicing.lean))

* Given a _sound policy slice_, the result of authorization is the same with the slice as it is with the full policy store.
