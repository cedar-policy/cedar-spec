include "core.dfy"

// Code for policy templates

module def.templates {
  import opened core

  // ----- Common definitions for policy templating ----- //

  // In the production engine as of this writing (2023-01-13), SlotId is an enum
  // of `Principal` and `Resource`, but doing that in the definitional engine
  // would complicate serialization for no benefit.
  type SlotId = string

  // Currently, slots are only ever filled with entity UIDs.
  type SlotEnv = map<SlotId, EntityUID>

  // A datatype that gives the "slot requirements" of a data structure, i.e.,
  // the information we need in order to determine whether a given SlotEnv is
  // valid to instantiate the data structure.
  //
  // Currently, this is just the set of slot IDs, but in the future, if we
  // support slots in `when` clauses, we might need to distinguish between slots
  // in the policy head (which can only be filled with entity UIDs if we want
  // the instantiated policy to be syntactically valid) and slots in `when`
  // clauses (which can be filled with any Cedar value as far as the runtime
  // semantics is concerned).
  type SlotReqs = set<SlotId>
  const emptySlotReqs: SlotReqs := {}

  predicate slotEnvSatisfiesReqs(se: SlotEnv, sr: SlotReqs) {
    se.Keys >= sr
  }

  // Compute the SlotReqs of a composite data structure from the SlotReqs of its
  // parts. Currently just set union; might become more complicated if we have
  // different kinds of slots in the future.
  function combineSlotReqs(sr1: SlotReqs, sr2: SlotReqs): SlotReqs {
    sr1 + sr2
  }

  // ----- Definitions of specific templated data structures ----- //

  // For certain Cedar data structures (e.g., `Policy`), there is some code in
  // CedarDafny that wants a version that allows slots and other code that wants
  // a version with no slots. As of this writing (2023-02-01), the
  // production engine has only one version of each data structure, which allows
  // slots, and code that doesn't expect a slot just raises an assertion error
  // if it runs into one. That approach isn't viable for CedarDafny, where
  // functions need to be defined on all inputs; we need two different
  // datatypes. We name them according to the scheme `Foo` and `FooTemplate`.
  // This differs from production, in which the single datatype that allows
  // slots is named `Foo` (except for the top-level `Template`, which is handled
  // specially); the naming difference seems sensible given our needs.
  //
  // Currently, we just write out separate definitions of `Foo` and
  // `FooTemplate`. This leads to some code duplication, both in the definitions
  // themselves and in any code that needs to accept both `Foo` and
  // `FooTemplate`. In the hope of avoiding this code duplication, we explored
  // an alternative design in which `Foo` is a subset type of `FooTemplate` with
  // empty SlotReqs. In principle, this subset type should work just like a
  // handwritten datatype without slots, assuming that the verifier
  // automatically propagates the "empty SlotReqs" condition down to subterms
  // and uses it to rule out "slot" cases during pattern matches. Unfortunately,
  // we found that the verifier had trouble with this reasoning and we believe
  // the problems would get worse in the future, so for now (2023-02-01), we
  // consider the code duplication to be the lesser evil.

  datatype PolicyTemplateID = PolicyTemplateID(id: string)

  datatype PolicyTemplate = PolicyTemplate(
    effect: Effect,
    principalScope: PrincipalScopeTemplate,
    actionScope: ActionScope,
    resourceScope: ResourceScopeTemplate,
    body: Expr)
  {
    function slotReqs(): SlotReqs {
      combineSlotReqs(principalScope.slotReqs(), resourceScope.slotReqs())
    }
  }

  datatype PrincipalScopeTemplate = PrincipalScopeTemplate(scope: ScopeTemplate)
  {
    function slotReqs(): SlotReqs {
      scope.slotReqs()
    }
  }

  datatype ResourceScopeTemplate = ResourceScopeTemplate(scope: ScopeTemplate)
  {
    function slotReqs(): SlotReqs {
      scope.slotReqs()
    }
  }

  // Note: This differs from the production `EntityReference` by having a
  // `slotId` field. The alternative (as seen in the production engine) is to
  // pass an extra `slotId` parameter through several functions. I (Matt) find
  // this design somewhat easier to understand (which is a design goal of the
  // definitional engine) and believe that justifies the difference from
  // production.
  datatype EntityUIDOrSlot = EntityUID(entity: EntityUID) | Slot(slotId: SlotId)
  {
    function slotReqs(): SlotReqs {
      match this {
        case EntityUID(_) => emptySlotReqs
        case Slot(slotId) => {slotId}
      }
    }
  }

  datatype ScopeTemplate = Any | Eq(entityOrSlot: EntityUIDOrSlot) | In(entityOrSlot: EntityUIDOrSlot)
  {
    function slotReqs(): SlotReqs {
      match this {
        case Any => emptySlotReqs
        case _ => entityOrSlot.slotReqs()
      }
    }
  }

  // Corresponds to production `Policy`. In the definitional engine, the
  // datatype for a non-template policy body has a much stronger claim to the
  // `Policy` name.
  datatype PolicyInstance =
    PolicyInstance(tid: PolicyTemplateID, slotEnv: SlotEnv)

  datatype TemplatedPolicyStoreUnvalidated = TemplatedPolicyStore(
    templates: map<PolicyTemplateID, PolicyTemplate>,
    instances: map<PolicyID, PolicyInstance>) {
    predicate isValid() {
      // Note: The production engine requires that each zero-slot template has
      // exactly one instance because a violation of that property is almost
      // certainly a mistake, but we don't enforce this in the definitional
      // engine because it would add complexity for no benefit.
      forall iid <- instances.Keys ::
        instances[iid].tid in templates.Keys &&
        // Note: As in the production engine, this is a stronger condition than
        // `slotEnvSatisfiesReqs(instances[iid].slotEnv, templates[instances[iid].tid].slotReqs())`:
        // for uniformity, we require all instances of a given template to
        // define exactly the slots actually referenced in the template and no
        // more.
        instances[iid].slotEnv.Keys == templates[instances[iid].tid].slotReqs()
    }
  }
  type TemplatedPolicyStore = tps: TemplatedPolicyStoreUnvalidated | tps.isValid()
    witness *

  datatype TemplatedStore = TemplatedStore(entities: EntityStore, policies: TemplatedPolicyStore)

  // ----- Code to instantiate templated data structures ----- //

  // Group all the functions that take a `slotEnv` parameter into a single
  // datatype to save us the boilerplate of passing the parameter along
  // explicitly.
  datatype Instantiator = Instantiator(slotEnv: SlotEnv) {
    predicate reqsSatisfied(sr: SlotReqs) {
      slotEnvSatisfiesReqs(slotEnv, sr)
    }

    function instantiateEntityUIDOrSlot(es: EntityUIDOrSlot): EntityUID
      requires reqsSatisfied(es.slotReqs())
    {
      match es {
        case EntityUID(e) => e
        case Slot(slotId) => slotEnv[slotId]
      }
    }

    function instantiateScope(st: ScopeTemplate): Scope
      requires reqsSatisfied(st.slotReqs())
    {
      match st {
        case Any => Scope.Any
        case In(e) => Scope.In(instantiateEntityUIDOrSlot(e))
        case Eq(e) => Scope.Eq(instantiateEntityUIDOrSlot(e))
      }
    }

    function instantiatePrincipalScope(pst: PrincipalScopeTemplate): PrincipalScope
      requires reqsSatisfied(pst.slotReqs())
    {
      PrincipalScope(instantiateScope(pst.scope))
    }

    function instantiateResourceScope(rst: ResourceScopeTemplate): ResourceScope
      requires reqsSatisfied(rst.slotReqs())
    {
      ResourceScope(instantiateScope(rst.scope))
    }

    function instantiatePolicy(pt: PolicyTemplate): Policy
      requires reqsSatisfied(pt.slotReqs())
    {
      Policy(
        pt.effect,
        instantiatePrincipalScope(pt.principalScope),
        pt.actionScope,
        instantiateResourceScope(pt.resourceScope),
        pt.body)
    }
  }

  function instantiatePolicyStore(tps: TemplatedPolicyStore): PolicyStore {
    PolicyStore(
      map iid <- tps.instances.Keys ::
        (var inst := tps.instances[iid];
         Instantiator(inst.slotEnv).instantiatePolicy(tps.templates[inst.tid])))
  }

  function instantiateStore(ts: TemplatedStore): Store {
    Store(ts.entities, instantiatePolicyStore(ts.policies))
  }
}
