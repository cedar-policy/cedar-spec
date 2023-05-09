# Cedar Dafny

This folder contains the Dafny formalization of, and proofs about, Cedar.

## Key definitions

Definitional engine (`def/*`)

* `Evaluator.interpret` returns the result of evaluating an expression
* `Authorizer.evaluate` returns the result of evaluating a policy
* `Authorizer.isAuthorized` checks whether a request is allowed or denied given the current policy store

Definitional validator (`validator/*`)

* `Typechecker.typecheck` checks if an expression matches a particular type according to permissive typechecking
* `StrictTypechecker.typecheck` checks if an expression matches a particular type according to strict typechecking
* `Validator.validate` validates a set of policies

## Verified properties

Basic theorems (`thm/basic.dfy`)

* If some forbid policy is satisfied, then the request is denied.
* A request is allowed only if it is explicitly permitted (i.e., there is at least one permit policy that is satisfied).
* If not explicitly permitted, a request is denied.

Sound policy slicing (`thm/slicing.dfy` and `thm/pslicing.dfy`)

* Given a _sound slice_, the result of authorization is the same with the slice as it is with the full store.

Type soundness (`validation/thm/toplevel.dfy`)

* If an expression is well-typed according to the typechecker, then either evaluation returns a value of that type or it returns an error of type `EntityDoesNotExist` or `ExtensionError`. All other errors are impossible.
