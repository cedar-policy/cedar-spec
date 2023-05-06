include "../def/all.dfy"
include "subtyping.dfy"
include "typechecker.dfy"
include "types.dfy"
include "util.dfy"

// This module contains the specification of Cedar's validator.
module validation.validator {
  import opened def.base
  import opened def.core
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

  // A Validator typechecks a set of policies.
  datatype Validator = Validator(schema: Schema) {
    // Returns a list of type errors for easier debugging,
    // but DRT currently only checks whether the output is empty.
    method Validate (policyStore: PolicyStore) returns (errs:seq<TypeError>)
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
          var typechecker := Typechecker(ets, acts, reqty);
          // substitute Action variable for a literal EUID
          var condition := substitute(p.toExpr(), Action, reqty.action);
          // check that p is a bool-typed expression under env
          var answer := typechecker.typecheck(condition, Type.Bool(AnyBool));
          match answer {
            case Ok(Bool(False)) => {}
            case Ok(_) => allFalse := false;
            case Err(e) =>
              allFalse := false;
              errs := errs + [e];
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
