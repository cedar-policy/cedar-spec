include "../../def/all.dfy"
include "../all.dfy"
include "base.dfy"
include "model.dfy"
include "soundness.dfy"

// This module contains the high-level statement of type soundness.
module validation.thm.toplevel {
  import opened strict
  import opened typechecker
  import opened types
  import opened base
  import opened model
  import opened soundness
  import opened def.core
  import opened def.engine

  datatype Schema = Schema(
    reqty: RequestType,
    ets: EntityTypeStore,
    acts: ActionStore
  )

  ghost predicate SatisfiesSchema(request: Request, entities: EntityStore, schema: Schema) {
    InstanceOfRequestType(request, schema.reqty) &&
    InstanceOfEntityTypeStore(entities, schema.ets) &&
    InstanceOfActionStore(entities, schema.acts)
  }

  function permissiveTypecheck(pid: PolicyID, policies: PolicyStore, schema: Schema): types.Result<Type>
    requires pid in policies.policies.Keys
  {
    var typechecker := Typechecker(schema.ets, schema.acts, schema.reqty);
    typechecker.typecheck(policies.policies[pid].toExpr(), Type.Bool(AnyBool))
  }

  // If an expression is well-typed according to the permissive typechecker,
  // then either evaluation returns a value of that type or it returns an error
  // of type EntityDoesNotExist or ExtensionError. All other errors (i.e.,
  // AttrDoesNotExist, TypeError, ArityMismatchError, NoSuchFunctionError) are
  // impossible.
  lemma PermissiveTypecheckingIsSound(
    pid: PolicyID,
    request: Request,
    store: Store,
    schema: Schema,
    res: base.Result<Value>,
    model: EvaluatorModel)
    requires pid in store.policies.policies.Keys
    requires SatisfiesSchema(request, store.entities, schema)
    requires permissiveTypecheck(pid, store.policies, schema).Ok?
    requires res == Evaluator(request, store.entities).interpret(store.policies.policies[pid].toExpr())
    ensures res.Ok? ==> InstanceOfType(res.value, Type.Bool(AnyBool))
    ensures res.Err? ==> res.error.EntityDoesNotExist? || res.error.ExtensionError?
  {
    var policies := store.policies;
    var entities := store.entities;
    var expr := policies.policies[pid].toExpr();
    assert model.IsSafe(request, entities, expr, Type.Bool(AnyBool)) by {
      SSP(model, schema.reqty, schema.ets, schema.acts, request, entities).SoundToplevel(expr, Type.Bool(AnyBool));
    }
  }

  function strictTypecheck(pid: PolicyID, policies: PolicyStore, schema: Schema): strict.Result<Type>
    requires pid in policies.policies.Keys
  {
    var typechecker := StrictTypechecker(schema.ets, schema.acts, schema.reqty);
    typechecker.typecheck(policies.policies[pid].toExpr(), Type.Bool(AnyBool))
  }

  // If an expression is well-typed according to the strict typechecker,
  // then either evaluation returns a value of that type or it returns an error
  // of type EntityDoesNotExist or ExtensionError. All other errors (i.e.,
  // AttrDoesNotExist, TypeError, ArityMismatchError, NoSuchFunctionError) are
  // impossible.
  lemma StrictTypecheckingIsSound(
    pid: PolicyID,
    request: Request,
    store: Store,
    schema: Schema,
    res: base.Result<Value>,
    model: EvaluatorModel)
    requires pid in store.policies.policies.Keys
    requires SatisfiesSchema(request, store.entities, schema)
    requires strictTypecheck(pid, store.policies, schema).Ok?
    requires res == Evaluator(request, store.entities).interpret(store.policies.policies[pid].toExpr())
    ensures res.Ok? ==> InstanceOfType(res.value, Type.Bool(AnyBool))
    ensures res.Err? ==> res.error.EntityDoesNotExist? || res.error.ExtensionError?
  {
    assert permissiveTypecheck(pid, store.policies, schema).Ok?;
    PermissiveTypecheckingIsSound(pid, request, store, schema, res, model);
  }
}
