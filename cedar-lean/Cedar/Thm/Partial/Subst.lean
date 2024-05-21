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
import Cedar.Thm.Partial.Evaluation.Basic

/-! ## Lemmas about `subst` operations -/

namespace Cedar.Thm.Partial.Subst

open Cedar.Data
open Cedar.Partial (Unknown)
open Cedar.Spec (Attr EntityUID)

/--
  subst on a concrete expression is that expression
-/
theorem subst_concrete_expr (expr : Spec.Expr) (subsmap : Map Unknown Partial.Value) :
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
theorem subst_concrete_value (value : Spec.Value) (subsmap : Map Unknown Partial.Value) :
  (Partial.Value.value value).subst subsmap = value
:= by
  unfold Partial.Value.subst
  split <;> rename_i h <;> simp only [Partial.Value.value.injEq] at h
  subst h
  rfl

/--
  Partial.Expr.subst on a concrete value is that value
-/
theorem subst_concrete_value' (value : Spec.Value) (subsmap : Map Unknown Partial.Value) :
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
theorem val_subst_preserves_wf {v v' : Partial.Value} {subsmap : Map Unknown Partial.Value} :
  v.WellFormed →
  v.subst subsmap = some v' →
  v'.WellFormed
:= by
  unfold Partial.Value.WellFormed Partial.Value.subst
  cases v <;> simp
  case value v =>
    intro h₁ h₂
    subst h₂
    simp [h₁]
  case residual r =>
    intro h₁
    subst h₁
    simp

/--
  Partial.Request.subst preserves well-formedness
-/
theorem req_subst_preserves_wf {req req' : Partial.Request} {subsmap : Map Unknown Partial.Value} :
  req.AllWellFormed →
  req.subst subsmap = some req' →
  req'.AllWellFormed
:= by
  unfold Partial.Request.AllWellFormed Partial.Request.subst
  intro wf h₁
  have ⟨wf_c, wf_vals⟩ := wf ; clear wf
  simp at h₁
  replace ⟨principal, _, ⟨action, _, ⟨resource, _, h₁⟩⟩⟩ := h₁
  subst h₁
  simp
  apply And.intro (Map.mapOnValues_wf.mp wf_c)
  intro pval' h₁
  rw [Map.values_mapOnValues] at h₁
  replace ⟨pval, h₁, h₂⟩ := List.mem_map.mp h₁
  subst pval'
  apply val_subst_preserves_wf (wf_vals pval h₁) (subsmap := subsmap)
  rfl

/--
  Partial.Request.subst preserves a known principal UID
-/
theorem req_subst_preserves_known_principal {req req' : Partial.Request} {uid : EntityUID} {subsmap : Map Unknown Partial.Value} :
  req.principal = .known uid →
  req.subst subsmap = some req' →
  req'.principal = .known uid
:= by
  intro h₁ h_req
  simp [Partial.Request.subst] at h_req
  replace ⟨principal, h_p, ⟨action, _, ⟨resource, _, h_req⟩⟩⟩ := h_req
  subst req'
  simp only
  simp [h₁, Partial.UidOrUnknown.subst] at h_p
  exact h_p.symm

/--
  Partial.Request.subst preserves a known action UID
-/
theorem req_subst_preserves_known_action {req req' : Partial.Request} {uid : EntityUID} {subsmap : Map Unknown Partial.Value} :
  req.action = .known uid →
  req.subst subsmap = some req' →
  req'.action = .known uid
:= by
  intro h₁ h_req
  simp [Partial.Request.subst] at h_req
  replace ⟨principal, _, ⟨action, h_a, ⟨resource, _, h_req⟩⟩⟩ := h_req
  subst req'
  simp only
  simp [h₁, Partial.UidOrUnknown.subst] at h_a
  exact h_a.symm

/--
  Partial.Request.subst preserves a known resource UID
-/
theorem req_subst_preserves_known_resource {req req' : Partial.Request} {uid : EntityUID} {subsmap : Map Unknown Partial.Value} :
  req.resource = .known uid →
  req.subst subsmap = some req' →
  req'.resource = .known uid
:= by
  intro h₁ h_req
  simp [Partial.Request.subst] at h_req
  replace ⟨principal, _, ⟨action, _, ⟨resource, h_r, h_req⟩⟩⟩ := h_req
  subst req'
  simp only
  simp [h₁, Partial.UidOrUnknown.subst] at h_r
  exact h_r.symm

/--
  Partial.Request.subst preserves the keyset of `context`
-/
theorem req_subst_preserves_keys_of_context {req req' : Partial.Request} {subsmap : Map Unknown Partial.Value} :
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
theorem req_subst_preserves_concrete_context_vals {req req' : Partial.Request} {k : Attr} {subsmap : Map Unknown Partial.Value} :
  (k, .value v) ∈ req.context.kvs →
  req.subst subsmap = some req' →
  (k, .value v) ∈ req'.context.kvs
:= by
  unfold Partial.Request.subst
  simp
  intro h₁ p _ a _ r _ h₂
  subst req'
  simp
  rw [← subst_concrete_value v subsmap]
  exact Map.in_kvs_in_mapOnValues h₁

/--
  Partial.EntityData.subst preserves well-formedness
-/
theorem entitydata_subst_preserves_wf {ed : Partial.EntityData} (subsmap : Map Unknown Partial.Value) :
  ed.WellFormed → (ed.subst subsmap).WellFormed
:= by
  unfold Partial.EntityData.WellFormed Partial.EntityData.subst
  intro h₁
  simp only
  and_intros
  · exact Map.mapOnValues_wf.mp h₁.left
  · exact h₁.right

/--
  Partial.Entities.subst preserves well-formedness
-/
theorem entities_subst_preserves_wf {entities : Partial.Entities} (subsmap : Map Unknown Partial.Value) :
  entities.AllWellFormed → (entities.subst subsmap).AllWellFormed
:= by
  unfold Partial.Entities.AllWellFormed Partial.Entities.subst
  intro h₁
  constructor
  · exact Map.mapOnValues_wf.mp h₁.left
  · intro ed' h₂
    simp [Map.values_mapOnValues] at h₂
    replace ⟨ed, h₂, h₃⟩ := h₂
    subst ed'
    exact entitydata_subst_preserves_wf subsmap (h₁.right ed h₂)

/--
  Partial.EntityData.subst preserves .ancestors
-/
theorem entitydata_subst_preserves_ancestors (ed : Partial.EntityData) (subsmap : Map Unknown Partial.Value) :
  ed.ancestors = (ed.subst subsmap).ancestors
:= by
  simp [Partial.EntityData.subst]

/--
  Partial.EntityData.subst preserves .contains on .attrs
-/
theorem entitydata_subst_preserves_contains_on_attrs (ed : Partial.EntityData) (attr : Attr) (subsmap : Map Unknown Partial.Value)
  (wf : ed.WellFormed) :
  ed.attrs.contains attr = (ed.subst subsmap).attrs.contains attr
:= by
  simp [Partial.EntityData.subst]
  unfold Partial.EntityData.WellFormed at wf
  apply Eq.symm
  cases h₁ : ed.attrs.contains attr
  case false =>
    rw [← Bool.not_eq_true] at *
    rw [Map.contains_iff_some_find?] at *
    simp at *
    intro pval h₂
    conv at h₁ => intro pval ; rw [← Map.in_list_iff_find?_some wf.left]
    rw [← Map.in_list_iff_find?_some (Map.mapOnValues_wf.mp wf.left)] at h₂
    simp [Map.mapOnValues, Map.kvs] at h₂
    replace ⟨(attr', pval'), h₂, h₃, h₄⟩ := h₂
    subst h₃ h₄
    simp [Map.kvs] at h₁
    exact h₁ pval' h₂
  case true =>
    rw [Map.contains_iff_some_find?] at *
    replace ⟨pval, h₁⟩ := h₁
    rw [← Map.in_list_iff_find?_some wf.left] at h₁
    exists (pval.subst subsmap)
    rw [← Map.in_list_iff_find?_some (Map.mapOnValues_wf.mp wf.left)]
    simp [Map.mapOnValues, Map.kvs]
    exists (attr, pval)

/--
  Partial.EntityData.subst preserves concrete attribute values
-/
theorem entitydata_subst_preserves_concrete_attrs {ed : Partial.EntityData} (subsmap : Map Unknown Partial.Value) :
  (k, .value v) ∈ ed.attrs.kvs → (k, .value v) ∈ (ed.subst subsmap).attrs.kvs
:= by
  simp [Partial.EntityData.subst]
  intro h₁
  rw [← subst_concrete_value v subsmap]
  exact Map.in_kvs_in_mapOnValues h₁

/--
  Partial.Entities.subst preserves .ancestorsOrEmpty
-/
theorem entities_subst_preserves_ancestorsOrEmpty (entities : Partial.Entities) (uid : EntityUID) (subsmap : Map Unknown Partial.Value) :
  entities.ancestorsOrEmpty uid = (entities.subst subsmap).ancestorsOrEmpty uid
:= by
  unfold Partial.Entities.subst Partial.Entities.ancestorsOrEmpty
  cases h₁ : entities.find? uid
  case none => simp [Map.find?_mapOnValues_none _ h₁]
  case some ed =>
    simp [Map.find?_mapOnValues_some _ h₁]
    exact entitydata_subst_preserves_ancestors ed subsmap

/--
  Partial.Entities.subst preserves concrete attribute values
-/
theorem entities_subst_preserves_concrete_attrs {entities : Partial.Entities} {uid : EntityUID} (subsmap : Map Unknown Partial.Value) :
  entities.attrs uid = .ok attrs →
  (k, .value v) ∈ attrs.kvs →
  ∃ attrs', (entities.subst subsmap).attrs uid = .ok attrs' ∧ (k, .value v) ∈ attrs'.kvs
:= by
  unfold Partial.Entities.subst Partial.Entities.attrs
  cases h₁ : entities.findOrErr uid Spec.Error.entityDoesNotExist <;> simp
  case ok ed =>
    intro h h₂ ; subst h
    have h₃ := entitydata_subst_preserves_concrete_attrs subsmap h₂
    exists (ed.subst subsmap).attrs
    apply And.intro _ h₃
    simp [Map.findOrErr_mapOnValues]
    simp [h₁, Except.map]

/--
  Partial.Entities.subst preserves `Map.contains` for the attrs maps
-/
theorem entities_subst_preserves_contains_on_attrsOrEmpty (entities : Partial.Entities) (uid : EntityUID) (attr : Attr) (subsmap : Map Unknown Partial.Value)
  (wf : entities.AllWellFormed) :
  (entities.attrsOrEmpty uid).contains attr = ((entities.subst subsmap).attrsOrEmpty uid).contains attr
:= by
  unfold Partial.Entities.subst Partial.Entities.attrsOrEmpty
  cases h₁ : entities.find? uid
  case none => simp [Map.find?_mapOnValues_none _ h₁]
  case some ed =>
    simp [Map.find?_mapOnValues_some _ h₁]
    apply entitydata_subst_preserves_contains_on_attrs ed attr subsmap
    unfold Partial.Entities.AllWellFormed at wf
    apply wf.right
    simp [← Map.in_list_iff_find?_some wf.left] at h₁
    exact Map.in_list_in_values h₁
