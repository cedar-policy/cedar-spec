include "../def/all.dfy"
include "subtyping.dfy"
include "typechecker.dfy"
include "types.dfy"
include "strict.dfy"
include "util.dfy"

// This module contains the specification of Cedar's validator.
module validation.validator {
  import opened def.base
  import opened def.core
  import opened strict
  import opened typechecker
  import opened types
  import opened util

  // The Schema file records various information useful for validation. Its
  // structure matches the Rust implementation to facilitate DRT.
  datatype Schema = Schema(
    entityTypes: map<EntityType, TypecheckerEntityType>,
    actionIds: map<EntityUID, TypecheckerActionId>
  ) {

    // Return every schema-defined request type
    function allRequestTypes(): set<RequestType> {
      set a,p,r | a in actionIds.Keys &&
                  p in actionIds[a].appliesTo.principalApplySpec &&
                  r in actionIds[a].appliesTo.resourceApplySpec ::
        RequestType(p, a, r, actionIds[a].context)
    }

    // Generate an EntityTypeStore
    function makeEntityTypeStore(): EntityTypeStore {
      var types := map et | et in entityTypes :: entityTypes[et].attributes;
      var descendants := map et | et in entityTypes :: entityTypes[et].descendants;
      EntityTypeStore(types, descendants)
    }

    // Generate an ActionStore
    function makeActionStore(): ActionStore {
      var descendants := map act | act in actionIds :: actionIds[act].descendants;
      ActionStore(descendants)
    }
  }

  datatype TypecheckerEntityType = TypecheckerEntityType(
    descendants: set<EntityType>,
    attributes: map<Attr, AttrType>
  )

  datatype TypecheckerActionId = TypecheckerActionId(
    appliesTo: TypecheckerApplySpec,
    descendants: set<EntityUID>,
    context: map<Attr, AttrType>
  )

  datatype TypecheckerApplySpec = TypecheckerApplySpec(
    principalApplySpec: set<Option<EntityType>>,
    resourceApplySpec: set<Option<EntityType>>
  )

  datatype ValidationError =
    // Error when typechecking a policy
    StrictTypeError(StrictTypeError) |
    // A policy returns False under all query types
    AllFalse

  // The ValidationMode determines whether to use permissive or strict typechecking
  datatype ValidationMode = Permissive | Strict

  // A Validator typechecks a set of policies.
  datatype Validator = Validator(schema: Schema, mode: ValidationMode) {

    // check that e is a bool-typed expression for the input entity store type,
    // action store, and request type
    function Typecheck (e: Expr, ets: EntityTypeStore, acts: ActionStore, reqty: RequestType): std.Result<Type, StrictTypeError> {
      if mode.Permissive?
      then match Typechecker(ets, acts, reqty).typecheck(e, Type.Bool(AnyBool)) {
        case Ok(ty) => std.Ok(ty)
        case Err(er) => std.Err(strict.TypeError(er))
      }
      else StrictTypechecker(ets, acts, reqty).typecheck(e, Type.Bool(AnyBool))
    }

    // Returns a list of type errors for easier debugging,
    // but DRT currently only checks whether the output is empty.
    method Validate (policyStore: PolicyStore) returns (errs:seq<ValidationError>)
    {
      var pset := set p | p in policyStore.policies.Values;
      errs := [];
      // for every policy p
      while pset != {} {
        var p :| p in pset;
        var reqtys := schema.allRequestTypes();
        var ets := schema.makeEntityTypeStore();
        var acts := schema.makeActionStore();
        // for every possible request type
        var allFalse := true;
        while reqtys != {} {
          var reqty :| reqty in reqtys;
          // substitute Action variable for a literal EUID
          var condition := substitute(p.toExpr(), Action, reqty.action);
          // typecheck p
          var answer := Typecheck(condition, ets, acts, reqty);
          match answer {
            case Ok(Bool(False)) => {}
            case Ok(_) => allFalse := false;
            case Err(e) =>
              allFalse := false;
              errs := errs + [StrictTypeError(e)];
          }
          reqtys := reqtys - { reqty };
        }
        // is the policy False under all envs?
        if allFalse {
          errs := errs + [AllFalse];
        }
        pset := pset - { p };
      }
      return errs;
    }
  }
}
