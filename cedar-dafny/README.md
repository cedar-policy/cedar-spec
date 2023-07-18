# Cedar Dafny

This folder contains the Dafny formalization of, and proofs about, Cedar.

## Key definitions

Definitional engine ([`def/*`](def/))

* [`Evaluator.interpret`](def/engine.dfy#L81) returns the result of evaluating an expression
* [`Authorizer.evaluate`](def/engine.dfy#L37) returns the result of evaluating a policy
* [`Authorizer.isAuthorized`](def/engine.dfy#L69) checks whether a request is allowed or denied given the current policy store

Definitional validator ([`validation/*`](validation))

* [`Typechecker.typecheck`](validation/typechecker.dfy#L648) checks if an expression matches a particular type according to permissive typechecking
* [`StrictTypechecker.typecheck`](validation/strict.dfy#L129) checks if an expression matches a particular type according to strict typechecking
* [`Validator.validate`](validation/validator.dfy#L103) validates a set of policies

## Verified properties

Basic theorems ([`thm/basic.dfy`](thm/basic.dfy))

* If some forbid policy is satisfied, then the request is denied.
* A request is allowed only if it is explicitly permitted (i.e., there is at least one permit policy that is satisfied).
* If not explicitly permitted, a request is denied.

Sound policy slicing ([`thm/slicing.dfy`](thm/slicing.dfy) and [`thm/pslicing.dfy`](thm/pslicing.dfy))

* Given a _sound slice_, the result of authorization is the same with the slice as it is with the full store.

Type soundness ([`validation/thm/toplevel.dfy`](validation/thm/toplevel.dfy))

* If an expression is well-typed according to the typechecker, then either evaluation returns a value of that type or it returns an error of type `EntityDoesNotExist` or `ExtensionError`. All other errors are impossible.
