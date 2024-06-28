/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Cedar.Data.Map
import Cedar.Partial.Entities
import Cedar.Partial.Expr
import Cedar.Partial.Request
import Cedar.Partial.Value
import Cedar.Spec.Expr
import Cedar.Thm.Data.List
import Cedar.Thm.Data.LT
import Cedar.Thm.Partial.Evaluation.WellFormed

/-! ## Lemmas about `subst` operations -/

namespace Cedar.Thm.Partial.Subst

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Attr EntityUID Error)

/--
  subst on a concrete expression is that expression
-/
theorem subst_concrete_expr (expr : Spec.Expr) (subsmap : Subsmap) :
  expr.asPartialExpr.subst subsmap = expr.asPartialExpr
:= by
  unfold Partial.Expr.subst Spec.Expr.asPartialExpr
  cases expr
  case lit | var => simp only
  case unaryApp op x₁ | getAttr x₁ attr | hasAttr x₁ attr =>
    simp only [Partial.Expr.unaryApp.injEq, Partial.Expr.getAttr.injEq, Partial.Expr.hasAttr.injEq, true_and, and_true]
    exact subst_concrete_expr x₁ subsmap
  case and x₁ x₂ | or x₁ x₂ | binaryApp op x₁ x₂ =>
    simp only [Partial.Expr.and.injEq, Partial.Expr.or.injEq, Partial.Expr.binaryApp.injEq, true_and, and_true]
    constructor
    · exact subst_concrete_expr x₁ subsmap
    · exact subst_concrete_expr x₂ subsmap
  case ite x₁ x₂ x₃ =>
    simp only [Partial.Expr.ite.injEq]
    and_intros
    · exact subst_concrete_expr x₁ subsmap
    · exact subst_concrete_expr x₂ subsmap
    · exact subst_concrete_expr x₃ subsmap
  case set xs | call xfn xs =>
    simp only [Partial.Expr.set.injEq, Partial.Expr.call.injEq, true_and, and_true]
    simp only [List.map₁_eq_map, List.map_map]
    apply List.map_congr
    intro x _
    exact subst_concrete_expr x subsmap
  case record attrs =>
    simp only [Partial.Expr.record.injEq, Partial.Expr.record.injEq, true_and, and_true]
    simp only [List.map_attach₂_snd, List.map_map]
    apply List.map_congr
    intro (a, x) h₁
    simp only [Function.comp_apply, Prod.mk.injEq, true_and]
    have := List.sizeOf_snd_lt_sizeOf_list h₁
    exact subst_concrete_expr x subsmap
termination_by expr

/--
  Partial.Value.subst on a concrete value is that value
-/
theorem subst_concrete_value (value : Spec.Value) (subsmap : Subsmap) :
  (Partial.Value.value value).subst subsmap = value
:= by
  unfold Partial.Value.subst
  split <;> rename_i h <;> simp only [Partial.Value.value.injEq] at h
  subst h
  rfl

/--
  Partial.Expr.subst on a concrete value is that value
-/
theorem subst_concrete_value' (value : Spec.Value) (subsmap : Subsmap) :
  value.asPartialExpr.subst subsmap = value.asPartialExpr
:= by
  unfold Partial.Expr.subst Spec.Value.asPartialExpr
  cases value
  case prim => simp only
  case set vs =>
    simp only [Partial.Expr.set.injEq]
    rw [List.map₁_eq_map, List.map₁_eq_map]
    rw [List.map_map]
    apply List.map_congr
    intro v _
    exact subst_concrete_value' v subsmap
  case record attrs =>
    simp only [Partial.Expr.record.injEq]
    rw [List.map_attach₂_snd]
    rw [List.map_attach₃_snd]
    rw [List.map_map]
    apply List.map_congr
    intro (k, v) _
    simp only [Function.comp_apply, Prod.mk.injEq, true_and]
    exact subst_concrete_value' v subsmap
  case ext x =>
    cases x <;> simp only [Partial.Expr.call.injEq, true_and]
    <;> rw [List.map₁_eq_map]
    <;> simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    <;> unfold Partial.Expr.subst
    <;> rfl
termination_by value
decreasing_by
  all_goals simp_wf
  case _ h₁ => -- set
    have := Set.sizeOf_lt_of_mem h₁
    omega
  case _ h₁ => -- record
    have h₂ := Map.sizeOf_lt_of_value h₁
    have h₃ := Map.sizeOf_lt_of_kvs m
    simp [Map.kvs] at h₂ h₃
    omega

/--
  Partial.Value.subst preserves well-formedness
-/
theorem val_subst_preserves_wf {v : Partial.Value} {subsmap : Subsmap} :
  v.WellFormed → (v.subst subsmap).WellFormed
:= by
  cases v <;> simp [Partial.Value.WellFormed, Partial.Value.subst]

/--
  Partial.Request.subst preserves well-formedness
-/
theorem req_subst_preserves_wf {req req' : Partial.Request} {subsmap : Subsmap} :
  req.WellFormed →
  req.subst subsmap = some req' →
  req'.WellFormed
:= by
  unfold Partial.Request.WellFormed Partial.Request.subst
  intro wf h₁
  have ⟨wf_c, wf_vals⟩ := wf ; clear wf
  simp only [Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h₁
  replace ⟨principal, _, ⟨action, _, ⟨resource, _, h₁⟩⟩⟩ := h₁
  subst h₁ ; simp only
  apply And.intro (Map.mapOnValues_wf.mp wf_c)
  intro pval' h₁
  rw [Map.values_mapOnValues] at h₁
  replace ⟨pval, h₁, h₂⟩ := List.mem_map.mp h₁
  subst pval'
  exact val_subst_preserves_wf (wf_vals pval h₁)

/--
  Partial.Request.subst preserves a known principal UID
-/
theorem req_subst_preserves_known_principal {req req' : Partial.Request} {uid : EntityUID} {subsmap : Subsmap} :
  req.principal = .known uid →
  req.subst subsmap = some req' →
  req'.principal = .known uid
:= by
  intro h₁ h_req
  simp only [Partial.Request.subst, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h_req
  replace ⟨principal, h_p, ⟨action, _, ⟨resource, _, h_req⟩⟩⟩ := h_req
  subst req'
  simp only
  simp only [Partial.UidOrUnknown.subst, h₁, Option.some.injEq] at h_p
  exact h_p.symm

/--
  Partial.Request.subst preserves a known action UID
-/
theorem req_subst_preserves_known_action {req req' : Partial.Request} {uid : EntityUID} {subsmap : Subsmap} :
  req.action = .known uid →
  req.subst subsmap = some req' →
  req'.action = .known uid
:= by
  intro h₁ h_req
  simp only [Partial.Request.subst, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h_req
  replace ⟨principal, _, ⟨action, h_a, ⟨resource, _, h_req⟩⟩⟩ := h_req
  subst req'
  simp only
  simp only [Partial.UidOrUnknown.subst, h₁, Option.some.injEq] at h_a
  exact h_a.symm

/--
  Partial.Request.subst preserves a known resource UID
-/
theorem req_subst_preserves_known_resource {req req' : Partial.Request} {uid : EntityUID} {subsmap : Subsmap} :
  req.resource = .known uid →
  req.subst subsmap = some req' →
  req'.resource = .known uid
:= by
  intro h₁ h_req
  simp only [Partial.Request.subst, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h_req
  replace ⟨principal, _, ⟨action, _, ⟨resource, h_r, h_req⟩⟩⟩ := h_req
  subst req'
  simp only
  simp only [Partial.UidOrUnknown.subst, h₁, Option.some.injEq] at h_r
  exact h_r.symm

/--
  Partial.Request.subst preserves the keyset of `context`
-/
theorem req_subst_preserves_keys_of_context {req req' : Partial.Request} {subsmap : Subsmap} :
  req.subst subsmap = some req' →
  req.context.keys = req'.context.keys
:= by
  unfold Partial.Request.subst
  simp only [Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq, forall_exists_index,
    and_imp]
  intro p _ a _ r _ _
  subst req' ; simp only
  exact (Map.keys_mapOnValues (Partial.Value.subst subsmap) req.context).symm

/--
  Partial.Request.subst preserves concrete values in the `context`
-/
theorem req_subst_preserves_concrete_context_vals {req req' : Partial.Request} {k : Attr} {subsmap : Subsmap} :
  (k, .value v) ∈ req.context.kvs →
  req.subst subsmap = some req' →
  (k, .value v) ∈ req'.context.kvs
:= by
  unfold Partial.Request.subst
  simp only [Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq, forall_exists_index,
    and_imp]
  intro h₁ p _ a _ r _ h₂
  subst req' ; simp only
  rw [← subst_concrete_value v subsmap]
  exact Map.in_kvs_in_mapOnValues h₁

/--
  Partial.EntityData.subst preserves well-formedness
-/
theorem entitydata_subst_preserves_wf {ed : Partial.EntityData} (subsmap : Subsmap) :
  ed.WellFormed → (ed.subst subsmap).WellFormed
:= by
  unfold Partial.EntityData.WellFormed Partial.EntityData.subst
  intro h₁
  and_intros
  · exact Map.mapOnValues_wf.mp h₁.left
  · exact h₁.right.left
  · intro pval h₂
    simp [Map.values_mapOnValues] at h₂
    replace ⟨pval', h₂, h₃⟩ := h₂
    subst h₃
    exact val_subst_preserves_wf (h₁.right.right pval' h₂)

/--
  Partial.Entities.subst preserves well-formedness
-/
theorem entities_subst_preserves_wf {entities : Partial.Entities} (subsmap : Subsmap) :
  entities.WellFormed → (entities.subst subsmap).WellFormed
:= by
  unfold Partial.Entities.WellFormed Partial.Entities.subst
  intro h₁
  constructor
  · exact Map.mapOnValues_wf.mp h₁.left
  · intro ed' h₂
    simp only [Map.values_mapOnValues, List.mem_map] at h₂
    replace ⟨ed, h₂, h₃⟩ := h₂
    subst ed'
    exact entitydata_subst_preserves_wf subsmap (h₁.right ed h₂)

/--
  Partial.EntityData.subst preserves .ancestors
-/
theorem entitydata_subst_preserves_ancestors (ed : Partial.EntityData) (subsmap : Subsmap) :
  ed.ancestors = (ed.subst subsmap).ancestors
:= by
  simp [Partial.EntityData.subst]

/--
  Partial.EntityData.subst preserves .contains on .attrs
-/
theorem entitydata_subst_preserves_contains_on_attrs (ed : Partial.EntityData) (attr : Attr) (subsmap : Subsmap)
  (wf : ed.WellFormed) :
  ed.attrs.contains attr = (ed.subst subsmap).attrs.contains attr
:= by
  unfold Partial.EntityData.subst
  unfold Partial.EntityData.WellFormed at wf
  apply Eq.symm
  cases h₁ : ed.attrs.contains attr
  case false =>
    rw [← Bool.not_eq_true] at *
    rw [Map.contains_iff_some_find?] at *
    simp only [not_exists] at *
    intro pval h₂
    conv at h₁ => intro pval ; rw [← Map.in_list_iff_find?_some wf.left]
    rw [← Map.in_list_iff_find?_some (Map.mapOnValues_wf.mp wf.left)] at h₂
    simp only [Map.kvs, Map.mapOnValues, List.mem_map, Prod.mk.injEq] at h₂
    replace ⟨(attr', pval'), h₂, h₃, h₄⟩ := h₂
    subst h₃ h₄
    simp only [Map.kvs] at h₁
    exact h₁ pval' h₂
  case true =>
    rw [Map.contains_iff_some_find?] at *
    replace ⟨pval, h₁⟩ := h₁
    rw [← Map.in_list_iff_find?_some wf.left] at h₁
    exists (pval.subst subsmap)
    rw [← Map.in_list_iff_find?_some (Map.mapOnValues_wf.mp wf.left)]
    simp only [Map.kvs, Map.mapOnValues, List.mem_map, Prod.mk.injEq]
    exists (attr, pval)

/--
  if an attr was present before Partial.EntityData.subst, then the substituted
  version of that attr is present after Partial.EntityData.subst
-/
theorem entitydata_subst_preserves_attrs {ed : Partial.EntityData} (subsmap : Subsmap) :
  (k, pval) ∈ ed.attrs.kvs → (k, pval.subst subsmap) ∈ (ed.subst subsmap).attrs.kvs
:= by
  unfold Partial.EntityData.subst
  exact Map.in_kvs_in_mapOnValues

/--
  Partial.EntityData.subst preserves concrete attribute values
-/
theorem entitydata_subst_preserves_concrete_attrs {ed : Partial.EntityData} (subsmap : Subsmap) :
  (k, .value v) ∈ ed.attrs.kvs → (k, .value v) ∈ (ed.subst subsmap).attrs.kvs
:= by
  intro h₁
  have h₂ := entitydata_subst_preserves_attrs subsmap h₁
  rw [subst_concrete_value] at h₂
  exact h₂

/--
  Partial.EntityData.subst preserves the absence of attribute values
-/
theorem entitydata_subst_preserves_absent_attrs {ed : Partial.EntityData} (subsmap : Subsmap) :
  k ∉ ed.attrs.keys → k ∉ (ed.subst subsmap).attrs.keys
:= by
  simp only [Partial.EntityData.subst, Map.keys_mapOnValues, imp_self]

/--
  Partial.Entities.subst preserves .ancestorsOrEmpty
-/
theorem entities_subst_preserves_ancestorsOrEmpty (entities : Partial.Entities) (uid : EntityUID) (subsmap : Subsmap) :
  entities.ancestorsOrEmpty uid = (entities.subst subsmap).ancestorsOrEmpty uid
:= by
  unfold Partial.Entities.subst Partial.Entities.ancestorsOrEmpty
  cases h₁ : entities.es.find? uid
  case none => simp only [Map.find?_mapOnValues_none _ h₁]
  case some ed =>
    simp only [Map.find?_mapOnValues_some _ h₁]
    exact entitydata_subst_preserves_ancestors ed subsmap

/--
  Partial.Entities.subst preserves absent entities
-/
theorem entities_subst_preserves_absent_entities {entities : Partial.Entities} {uid : EntityUID} (subsmap : Subsmap) :
  entities.es.find? uid = none → (entities.subst subsmap).es.find? uid = none
:= by
  simp only [Partial.Entities.subst]
  intro h
  exact Map.find?_mapOnValues_none _ h

/--
  Partial.Entities.subst preserves present entities
-/
theorem entities_subst_preserves_present_entities {entities : Partial.Entities} {uid : EntityUID} (subsmap : Subsmap) :
  entities.es.find? uid = some ed → ∃ ed', (entities.subst subsmap).es.find? uid = some ed'
:= by
  simp only [Partial.Entities.subst]
  intro h
  exists (ed.subst subsmap)
  exact Map.find?_mapOnValues_some _ h

/--
  if an attr was present before Partial.Entities.subst, then the substituted
  version of that attr is present after Partial.Entities.subst
-/
theorem entities_subst_preserves_attrs {entities : Partial.Entities} {uid : EntityUID} (subsmap : Subsmap) :
  entities.attrs uid = .ok attrs →
  (k, pval) ∈ attrs.kvs →
  ∃ attrs', (entities.subst subsmap).attrs uid = .ok attrs' ∧ (k, pval.subst subsmap) ∈ attrs'.kvs
:= by
  unfold Partial.Entities.subst Partial.Entities.attrs
  cases h₁ : entities.es.findOrErr uid Error.entityDoesNotExist
  case error e => simp only [Except.bind_err, false_implies]
  case ok ed =>
    simp only [Except.bind_ok, Except.ok.injEq]
    intro h h₂ ; subst h
    have h₃ := entitydata_subst_preserves_attrs subsmap h₂
    exists (ed.subst subsmap).attrs
    apply And.intro _ h₃
    simp only [Map.findOrErr_mapOnValues]
    simp only [h₁, Except.map, Except.bind_ok]

/--
  Partial.Entities.subst preserves concrete attribute values
-/
theorem entities_subst_preserves_concrete_attrs {entities : Partial.Entities} {uid : EntityUID} (subsmap : Subsmap) :
  entities.attrs uid = .ok attrs →
  (k, .value v) ∈ attrs.kvs →
  ∃ attrs', (entities.subst subsmap).attrs uid = .ok attrs' ∧ (k, .value v) ∈ attrs'.kvs
:= by
  intro h₁ h₂
  have h₃ := entities_subst_preserves_attrs subsmap h₁ h₂
  rw [subst_concrete_value] at h₃
  exact h₃

/--
  Partial.Entities.subst preserves the absence of attribute values
-/
theorem entities_subst_preserves_absent_attrs {entities : Partial.Entities} {uid : EntityUID} (subsmap : Subsmap) :
  entities.attrs uid = .ok attrs →
  k ∉ attrs.keys →
  ∃ attrs', (entities.subst subsmap).attrs uid = .ok attrs' ∧ k ∉ attrs'.keys
:= by
  -- structure of this proof is extremely similar to the proof of
  -- `entities_subst_preserves_attrs`, maybe they could be shared
  simp only [Partial.Entities.subst, Partial.Entities.attrs]
  cases h₁ : entities.es.findOrErr uid Error.entityDoesNotExist
  case error e => simp only [Except.bind_err, false_implies]
  case ok ed =>
    simp only [Except.bind_ok, Except.ok.injEq]
    intro h h₂ ; subst h
    have h₃ := entitydata_subst_preserves_absent_attrs subsmap h₂
    exists (ed.subst subsmap).attrs
    apply And.intro _ h₃
    simp only [Map.findOrErr_mapOnValues]
    simp only [h₁, Except.map, Except.bind_ok]

/--
  Partial.Entities.subst preserves errors returned by `Partial.Entities.attrs`
-/
theorem entities_subst_preserves_error_attrs {entities : Partial.Entities} {uid : EntityUID} (subsmap : Subsmap) :
  entities.attrs uid = .error e ↔ (entities.subst subsmap).attrs uid = .error e
:= by
  unfold Partial.Entities.subst Partial.Entities.attrs
  constructor
  case mp =>
    rcases Map.findOrErr_returns entities.es uid Error.entityDoesNotExist with h₁ | h₁
    · replace ⟨edata, h₁⟩ := h₁ ; simp [h₁]
    · simp [h₁]
      intro h₂ ; subst e
      rw [Map.findOrErr_err_iff_find?_none] at h₁
      cases h₂ : (entities.es.mapOnValues (Partial.EntityData.subst subsmap)).findOrErr uid Error.entityDoesNotExist
      case error e =>
        rcases Map.findOrErr_returns (entities.es.mapOnValues (Partial.EntityData.subst subsmap)) uid Error.entityDoesNotExist with h₃ | h₃
        <;> simp [h₂] at h₃
        · simp [h₃]
      case ok edata =>
        rw [Map.findOrErr_ok_iff_find?_some] at h₂
        simp [Map.find?_mapOnValues_none (Partial.EntityData.subst subsmap) h₁] at h₂
  case mpr =>
    rcases Map.findOrErr_returns (entities.subst subsmap).es uid Error.entityDoesNotExist with h₁ | h₁
    · replace ⟨edata, h₁⟩ := h₁
      unfold Partial.Entities.subst at h₁
      simp [h₁]
    · unfold Partial.Entities.subst at h₁
      simp [h₁]
      intro h₂ ; subst e
      rw [Map.findOrErr_err_iff_find?_none] at h₁
      cases h₂ : entities.es.findOrErr uid Error.entityDoesNotExist <;> simp
      case error e =>
        rcases Map.findOrErr_returns entities.es uid Error.entityDoesNotExist with h₃ | h₃
        <;> simp [h₂] at h₃
        · exact h₃
      case ok edata =>
        rw [Map.findOrErr_ok_iff_find?_some] at h₂
        have ⟨ed', h₃⟩ := entities_subst_preserves_present_entities subsmap h₂
        unfold Partial.Entities.subst at h₃
        simp [h₃] at h₁

/--
  Partial.Entities.subst preserves `Map.contains` for the attrs maps
-/
theorem entities_subst_preserves_contains_on_attrsOrEmpty (entities : Partial.Entities) (uid : EntityUID) (attr : Attr) (subsmap : Subsmap)
  (wf : entities.WellFormed) :
  (entities.attrsOrEmpty uid).contains attr = ((entities.subst subsmap).attrsOrEmpty uid).contains attr
:= by
  unfold Partial.Entities.subst Partial.Entities.attrsOrEmpty
  cases h₁ : entities.es.find? uid
  case none => simp only [Map.find?_mapOnValues_none _ h₁]
  case some ed =>
    simp only [Map.find?_mapOnValues_some _ h₁]
    apply entitydata_subst_preserves_contains_on_attrs ed attr subsmap
    unfold Partial.Entities.WellFormed at wf
    apply wf.right
    simp only [← Map.in_list_iff_find?_some wf.left] at h₁
    exact Map.in_list_in_values h₁
