/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

include "../def/all.dfy"
include "slicing.dfy"

// This module proves it is sound to slice policies based on head constraints
// (see AuthorizationIsCorrectForHeadBasedPolicySlicing and
// HeadBasedSlicingIsSound). The proof is based on a more general lemma
// (TargetBasedSlicingIsSound) that covers all forms of slicing that are based
// on identifying "target" principal and resource entities (if any) for a
// policy, such that the policy evaluates to true on an input only if the
// request principal and resource are descendents of the corresponding target
// entities. Currently, we are extracting targets only from the head
// constraints. The general lemma also covers more sophisticated analyses that
// can extract targets from policy conditions as well.
module pslicing {
  import opened def.base
  import opened def.core
  import opened def.engine
  import opened def.std
  import opened slicing

  // Optional target principal and resource entities for a policy.
  datatype Target =
    Target(
      principal: Option<EntityUID>,
      resource: Option<EntityUID>)
  {
    predicate satisfiedBy(request: Request, store: EntityStore)
    {
      var eval := Evaluator(request, store);
      (principal.None? ||
       eval.entityInEntity(request.principal, principal.value)) &&
      (resource.None? ||
       eval.entityInEntity(request.resource, resource.value))
    }
  }

  // A target analysis takes as input a policy and returns Target.
  type TargetAnalysis = Policy -> Target

  // A slicing function takes as input a policy and returns true iff
  // the policy should be included in a slice.
  type Slicer = Policy -> bool

  // Defines what it means for a target to be sound for a policy. Note that it's
  // always okay to specify no target entities. When specified, it must be the
  // case that the policy implies the membership of the principal or resource
  // variable in the corresponding target entities.
  ghost predicate isSoundTarget(tgt: Target, p: Policy) {
    forall request: Request, store: EntityStore |
      Evaluator(request, store).interpret(p.toExpr()) == Ok(Value.TRUE) ::
      tgt.satisfiedBy(request, store)
  }

  // A target analysis is sound if it produces sound targets for all policies.
  ghost predicate isSoundTargetAnalysis(ta: TargetAnalysis) {
    forall p: Policy :: isSoundTarget(ta(p), p)
  }

  // Takes a target analysis, request, and principal / resource ancestors, and
  // returns a slicer that can be passed as input to slicePolicies.
  function targetSlicer(
    ta: TargetAnalysis,
    request: Request,
    store: EntityStore):
    Slicer
  {
    (p: Policy) => ta(p).satisfiedBy(request, store)
  }

  function slicePolicies(
    store: PolicyStore,
    slicer: Slicer): (slice: PolicyStore)
    ensures isSliceOfPolicyStore(slice, store)
  {
    PolicyStore(
      map pid |
        pid in store.policies.Keys &&
        slicer(store.policies[pid]) ::
        store.policies[pid]
    )
  }

  // ----- Soundness of policy slicing using a sound target analysis ----- //

  // When based on a sound target analysis, policy slicing returns a
  // sound policy slice.
  lemma TargetBasedSlicingIsSound(ta: TargetAnalysis, request: Request, slice: Store, store: Store)
    requires isSoundTargetAnalysis(ta)
    requires slice.entities == store.entities
    requires slice.policies == slicePolicies(store.policies, targetSlicer(ta, request, store.entities))
    ensures isSoundSliceForRequest(request, slice, store)
  {
    forall pid | pid in store.policies.policies.Keys && pid !in slice.policies.policies.Keys
    {
      TargetBasedSlicingIsSoundAux(pid, ta(store.policies.policies[pid]), request, store);
    }
  }

  lemma TargetBasedSlicingIsSoundAux(pid: PolicyID, tgt: Target, request: Request, store: Store)
    requires pid in store.policies.policies.Keys
    requires isSoundTarget(tgt, store.policies.policies[pid])
    requires !tgt.satisfiedBy(request, store.entities)
    ensures !Authorizer(request, store).satisfied(pid)
  {
    var eval := Evaluator(request, store.entities);
    var p := store.policies.policies[pid];
    assert
      (tgt.principal.Some? &&
       !eval.entityInEntity(request.principal, tgt.principal.value)) ||
      (tgt.resource.Some? &&
       !eval.entityInEntity(request.resource, tgt.resource.value));
    assert eval.interpret(p.toExpr()) != Ok(Value.TRUE);
  }

  // ----- Soundness of policy slicing based on policy head targets ----- //

  function headBasedTarget(p: Policy): Target {
    Target(
      if p.principalScope.scope.Any? then None else Some(p.principalScope.scope.entity),
      if p.resourceScope.scope.Any? then None else Some(p.resourceScope.scope.entity))
  }

  function headBasedPolicySlice(request: Request, store: Store): PolicyStore {
    slicePolicies(store.policies, targetSlicer(headBasedTarget, request, store.entities))
  }

  lemma AuthorizationIsCorrectForHeadBasedPolicySlicing(request: Request, slice: Store, store: Store)
    requires slice.entities == store.entities
    requires slice.policies == headBasedPolicySlice(request, store)
    ensures Authorizer(request, slice).isAuthorized() == Authorizer(request, store).isAuthorized()
  {
    HeadBasedSlicingIsSound(request, slice, store);
    AuthorizationIsCorrectForSoundSlicing(request, slice, store);
  }

  lemma HeadBasedSlicingIsSound(request: Request, slice: Store, store: Store)
    requires slice.entities == store.entities
    requires slice.policies == headBasedPolicySlice(request, store)
    ensures isSoundSliceForRequest(request, slice, store)
  {
    forall p: Policy, q: Request, s: EntityStore |
      Evaluator(q, s).interpret(p.toExpr()) == Ok(Value.TRUE)
    {
      HeadBasedTargetIsSound(p, q, s);
    }
    TargetBasedSlicingIsSound(headBasedTarget, request, slice, store);
  }

  lemma HeadBasedTargetIsSound(p: Policy, request: Request, store: EntityStore)
    requires Evaluator(request, store).interpret(p.toExpr()) == Ok(Value.TRUE)
    ensures
      var tgt := headBasedTarget(p);
      tgt.satisfiedBy(request, store)
  {
    var tgt := headBasedTarget(p);
    var eval := Evaluator(request, store);
    PolicyConditionImpliesHead(p, eval);
    if tgt.principal.Some? {
      EntityInOrEqEntitySemantics(
        Var(Var.Principal),
        eval.request.principal,
        PrimitiveLit(Primitive.EntityUID(p.principalScope.scope.entity)),
        p.principalScope.scope.entity,
        eval);
    }
    if tgt.resource.Some? {
      EntityInOrEqEntitySemantics(
        Var(Var.Resource),
        eval.request.resource,
        PrimitiveLit(Primitive.EntityUID(p.resourceScope.scope.entity)),
        p.resourceScope.scope.entity,
        eval);
    }
  }

  lemma PolicyConditionImpliesHead(p: Policy, eval: Evaluator)
    requires eval.interpret(p.toExpr()) == Ok(Value.TRUE)
    ensures eval.interpret(p.principalScope.toExpr()) == Ok(Value.TRUE)
    ensures eval.interpret(p.resourceScope.toExpr()) == Ok(Value.TRUE)
  {
    var e1 := And(p.resourceScope.toExpr(), p.condition);
    var e2 := And(p.actionScope.toExpr(), e1);
    AndSemantics(p.principalScope.toExpr(), e2, eval);
    AndSemantics(p.actionScope.toExpr(), e1, eval);
    AndSemantics(p.resourceScope.toExpr(), p.condition, eval);
  }

  lemma EntityInOrEqEntitySemantics(x1: Expr, e1: EntityUID, x2: Expr, e2: EntityUID, eval: Evaluator)
    requires eval.interpret(x1) == Ok(Value.EntityUID(e1))
    requires eval.interpret(x2) == Ok(Value.EntityUID(e2))
    requires
      eval.interpret(BinaryApp(BinaryOp.In, x1, x2)) == Ok(Value.TRUE) ||
      eval.interpret(BinaryApp(BinaryOp.Eq, x1, x2)) == Ok(Value.TRUE)
    ensures eval.entityInEntity(e1, e2)
  { }

  lemma AndSemantics(e1: Expr, e2: Expr, eval: Evaluator)
    requires eval.interpret(And(e1, e2)) == Ok(Value.TRUE)
    ensures eval.interpret(e1) == Ok(Value.TRUE)
    ensures eval.interpret(e2) == Ok(Value.TRUE)
  { }
}
