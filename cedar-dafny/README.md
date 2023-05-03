# Cedar Dafny

This folder contains the Dafny formalization of, and proofs about, Cedar.

## Key definitions

Definitional engine (`def/*`)

* `Evaluator.interpret` returns the result of evaluating an expression
* `Authorizer.evaluate` returns the result of evaluating a policy
* `Authorizer.isAuthorized` checks if a request is allowed or denied given the current policy store

Definitional validator (`validator/*`)

* `Validator.infer` infers the type of an expression
* `Validator.typecheck` checks if an expression matches a particular type

## Verified properties

Basic theorems (`thm/basic.dfy`)

* If the policy set is empty, then every request is denied.
* If no permit policy is in force, then the request is denied.
* If some forbid policy is in force, then the request is denied.
* A request is allowed if and only if it is explicitly permitted, meaning that there is at least one permit policy that is in force and no forbid policies are in force.

Sound policy slicing (`thm/slicing.dfy` and `thm/pslicing.dfy`)

* Given a _sound slice_, the result of authorization is the same with the slice as it is with the full store.
