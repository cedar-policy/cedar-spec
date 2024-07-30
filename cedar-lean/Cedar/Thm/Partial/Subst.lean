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
import Cedar.Data.SizeOf
import Cedar.Partial.Entities
import Cedar.Partial.Request
import Cedar.Partial.Value
import Cedar.Spec.Expr
import Cedar.Thm.Data.List
import Cedar.Thm.Data.LT
import Cedar.Thm.Partial.Evaluation.Props
--import Cedar.Thm.Partial.IsRestricted
import Cedar.Thm.Partial.WellFormed

/-! ## Lemmas about `subst` operations -/

namespace Cedar.Thm.Partial.Subst

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Attr EntityUID Error Expr Prim)

/--
  Partial.Value.subst on a concrete value is that value
-/
theorem subst_concrete_value (value : Spec.Value) (subsmap : Subsmap) :
  (Partial.Value.value value).subst subsmap = value
:= by
  simp only [Partial.Value.subst]

/--
  If a list of `Partial.Value`s is all concrete, then mapping
  `Partial.Value.subst` over it does nothing
-/
theorem subst_concrete_values {pvals : List Partial.Value} {subsmap : Subsmap} :
  IsAllConcrete pvals →
  pvals = pvals.map (Partial.Value.subst subsmap)
:= match pvals with
  | [] => by simp only [List.map_nil, implies_true]
  | hd :: tl => by
    simp only [IsAllConcrete, List.mapM_cons, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_some, Option.some.injEq, List.map_cons, List.cons.injEq, forall_exists_index,
      and_imp]
    intro vs vhd
    exact match hd with
    | .residual r => by simp only [false_implies]
    | .value v => by
      simp only [Option.some.injEq]
      intro _ ; subst vhd
      intro vtl hvtl _ ; subst vs
      simp [Subst.subst_concrete_value]
      apply subst_concrete_values
      unfold IsAllConcrete
      exists vtl

private theorem sizeOf_elem_lt_sizeOf_prod [SizeOf α] [SizeOf β] (a : α) (b : β) :
  sizeOf b < sizeOf (a, b)
:= by
  conv => rhs ; simp [sizeOf, Prod._sizeOf_1]
  conv => lhs ; simp [sizeOf]
  omega

mutual

/--
  Partial.ResidualExpr.subst preserves well-formedness
-/
theorem residual_subst_preserves_wf {x : Partial.ResidualExpr} {subsmap : Subsmap} :
  x.WellFormed → subsmap.WellFormed → (x.subst subsmap).WellFormed
:= by
  cases x <;>
    simp only [Partial.ResidualExpr.WellFormed, Partial.ResidualExpr.subst,
      Partial.Value.WellFormed, and_imp, implies_true, true_implies, imp_self]
  case unknown u =>
    split
    · rename_i pv h
      intro wf_s
      simp only [Subsmap.WellFormed] at wf_s
      apply wf_s.right
      · replace h := Map.find?_mem_toList h
        exact Map.in_list_in_values h
    · simp only [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed, implies_true]
  case getAttr pv₁ attr | hasAttr pv₁ attr | unaryApp op attr =>
    exact val_subst_preserves_wf
  case and pv₁ pv₂ | or pv₁ pv₂ | binaryApp op pv₁ pv₂ =>
    intro wf₁ wf₂ wf_s
    and_intros
    · exact val_subst_preserves_wf wf₁ wf_s
    · exact val_subst_preserves_wf wf₂ wf_s
  case ite pv₁ pv₂ pv₃ =>
    intro wf₁ wf₂ wf₃ wf_s
    and_intros
    · exact val_subst_preserves_wf wf₁ wf_s
    · exact val_subst_preserves_wf wf₂ wf_s
    · exact val_subst_preserves_wf wf₃ wf_s
  case set pvs | call xfn pvs =>
    rw [List.map₁_eq_map]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro h₁ wf_s pv hpv
    exact val_subst_preserves_wf (h₁ pv hpv) wf_s
  case record apvs =>
    rw [List.map_attach₂_snd]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro h₁ wf_s (k, v) hkv
    exact val_subst_preserves_wf (h₁ (k, v) hkv) wf_s
termination_by sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals try omega
  case _ => -- set
    have := List.sizeOf_lt_of_mem hpv
    omega
  case _ => -- record
    have h₂ := List.sizeOf_lt_of_mem hkv
    have h₃ := sizeOf_elem_lt_sizeOf_prod k v
    omega
  case _ => -- call
    have := List.sizeOf_lt_of_mem hpv
    omega

/--
  Partial.Value.subst preserves well-formedness
-/
theorem val_subst_preserves_wf {pv : Partial.Value} {subsmap : Subsmap} :
  pv.WellFormed → subsmap.WellFormed → (pv.subst subsmap).WellFormed
:= match pv with
  | .value v => by simp only [Partial.Value.WellFormed, subst_concrete_value] ; intro h _ ; exact h
  | .residual r => by
    -- we want to unfold only the first occurrence of `Partial.Value.WellFormed`.
    -- I'm not aware of any way in Lean to do this directly, but this workaround works
    have h_tmp : (Partial.Value.residual r).WellFormed ↔ r.WellFormed := by
      simp only [Partial.Value.WellFormed]
    rw [h_tmp] ; clear h_tmp
    simp only [Partial.Value.subst]
    exact residual_subst_preserves_wf
termination_by sizeOf pv

end

/--
  Expr.substToPartialValue produces well-formed partial values
-/
theorem substToPartialValue_wf (x : Expr) {req : Partial.Request}
  (wf_r : req.WellFormed) :
  (x.substToPartialValue req).WellFormed
:= by
  cases x
  case var v =>
    cases v <;> simp only [Expr.substToPartialValue]
    case principal | action | resource =>
      split <;> simp only [Partial.Value.WellFormed, Spec.Value.WellFormed, Prim.WellFormed, Partial.ResidualExpr.WellFormed]
    case context =>
      simp only [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]
      unfold Partial.Request.WellFormed at wf_r
      split at wf_r ; rename_i context ; simp only
      intro (k, pv) hpv
      exact wf_r.right pv (Map.in_list_in_values hpv)
  all_goals simp only [Expr.substToPartialValue, Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]
  case lit p => simp only [Spec.Value.WellFormed, Prim.WellFormed]
  case getAttr x₁ attr | hasAttr x₁ attr | unaryApp op x₁ =>
    exact substToPartialValue_wf x₁ wf_r
  case and x₁ x₂ | or x₁ x₂ | binaryApp op x₁ x₂ =>
    and_intros
    · exact substToPartialValue_wf x₁ wf_r
    · exact substToPartialValue_wf x₂ wf_r
  case ite x₁ x₂ x₃ =>
    and_intros
    · exact substToPartialValue_wf x₁ wf_r
    · exact substToPartialValue_wf x₂ wf_r
    · exact substToPartialValue_wf x₃ wf_r
  case set xs | call xfn xs =>
    rw [List.map₁_eq_map]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro x _
    exact substToPartialValue_wf x wf_r
  case record axs =>
    simp only [List.map_attach₂_snd, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro (k, x) _
    exact substToPartialValue_wf x wf_r
termination_by x
decreasing_by
  all_goals simp_wf
  all_goals try omega
  case _ h₁ => -- set
    have := List.sizeOf_lt_of_mem h₁
    omega
  case _ h₁ => -- record
    have h₂ := List.sizeOf_lt_of_mem h₁
    have h₃ := sizeOf_elem_lt_sizeOf_prod k x
    omega
  case _ h₁ => -- call
    have := List.sizeOf_lt_of_mem h₁
    omega

/--
  Partial.Request.subst preserves well-formedness
-/
theorem req_subst_preserves_wf {req req' : Partial.Request} {subsmap : Subsmap} :
  req.WellFormed →
  subsmap.WellFormed →
  req.subst subsmap = some req' →
  req'.WellFormed
:= by
  unfold Partial.Request.WellFormed Partial.Request.subst
  intro wf_r wf_s h₁
  have ⟨wf_c, wf_vals⟩ := wf_r ; clear wf_r
  simp only [Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h₁
  replace ⟨principal, _, ⟨action, _, ⟨resource, _, h₁⟩⟩⟩ := h₁
  subst h₁ ; simp only
  apply And.intro (Map.mapOnValues_wf.mp wf_c)
  intro pval' h₁
  rw [Map.values_mapOnValues] at h₁
  replace ⟨pval, h₁, h₂⟩ := List.mem_map.mp h₁
  subst pval'
  exact val_subst_preserves_wf (wf_vals pval h₁) wf_s

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
  ed.WellFormed → subsmap.WellFormed → (ed.subst subsmap).WellFormed
:= by
  unfold Partial.EntityData.WellFormed Partial.EntityData.subst
  intro h₁ h₂
  and_intros
  · exact Map.mapOnValues_wf.mp h₁.left
  · exact h₁.right.left
  · intro pval h₃
    simp [Map.values_mapOnValues] at h₃
    replace ⟨pval', h₃, h₄⟩ := h₃
    subst h₄
    exact val_subst_preserves_wf (h₁.right.right pval' h₃) h₂

/--
  Partial.Entities.subst preserves well-formedness
-/
theorem entities_subst_preserves_wf {entities : Partial.Entities} {subsmap : Subsmap} :
  entities.WellFormed → subsmap.WellFormed → (entities.subst subsmap).WellFormed
:= by
  unfold Partial.Entities.WellFormed Partial.Entities.subst
  intro h₁ h₂
  constructor
  · exact Map.mapOnValues_wf.mp h₁.left
  · intro ed' h₃
    simp only [Map.values_mapOnValues, List.mem_map] at h₃
    replace ⟨ed, h₃, h₄⟩ := h₃
    subst ed'
    exact entitydata_subst_preserves_wf subsmap (h₁.right ed h₃) h₂

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
    simp only [Map.findOrErr_mapOnValues, Except.map, h₁, Except.bind_ok, Except.ok.injEq,
      exists_eq_left']
    exact entitydata_subst_preserves_attrs subsmap h₂

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
    simp only [Map.findOrErr_mapOnValues, Except.map, h₁, Except.bind_ok, Except.ok.injEq,
      exists_eq_left']
    exact entitydata_subst_preserves_absent_attrs subsmap h₂

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
        · simp only [h₂, exists_const] at h₃
        · simpa [h₂] using h₃
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

/--
  Variant of `entities_subst_preserves_attrs` for `Partial.attrsOf`
-/
theorem attrsOf_subst_preserves_attrs {v₁ : Spec.Value} {entities : Partial.Entities} (subsmap : Subsmap)
  (wf_v : v₁.WellFormed) :
  Partial.attrsOf v₁ entities.attrs = .ok attrs →
  (k, pval) ∈ attrs.kvs →
  ∃ attrs', Partial.attrsOf v₁ (entities.subst subsmap).attrs = .ok attrs' ∧ (k, pval.subst subsmap) ∈ attrs'.kvs
:= by
  cases v₁ <;> simp [Partial.attrsOf]
  case prim p₁ =>
    cases p₁ <;> simp
    case entityUID uid => exact entities_subst_preserves_attrs subsmap
  case record r₁ =>
    simp only [Spec.Value.WellFormed] at wf_v
    intro _ ; subst attrs
    exact match pval with
    | .value v => by simp [Subst.subst_concrete_value]
    | .residual r => by
      intro h₁
      replace h₁ := Map.in_mapOnValues_in_kvs' wf_v.left h₁
      simp at h₁

/--
  `Partial.Value.subst` on the result of `Spec.Expr.substToPartialValue`
  gives the same result as if we first substitute the `req` and then do
  `Spec.Expr.substToPartialValue`
-/
theorem subst_substToPartialValue (x : Spec.Expr) {req : Partial.Request} {subsmap : Subsmap} :
  req.subst subsmap = some req' →
  (x.substToPartialValue req).subst subsmap = x.substToPartialValue req'
:= by
  cases x
  case var v =>
    simp [Partial.Request.subst]
    intro p' h_p' a' h_a' r' h_r' h_req ; subst h_req
    cases v <;> simp only [Spec.Expr.substToPartialValue]
    case principal =>
      cases h_p : req.principal <;> cases p'
      <;> simp [Partial.Value.subst, Partial.ResidualExpr.subst]
      <;> simp [h_p, Partial.UidOrUnknown.subst] at h_p'
      case known.known => exact h_p'
      case unknown.unknown u₁ u₂ =>
        split at h_p' <;> rename_i h_p'' <;> simp at h_p'
        · subst u₂ ; rename_i u₂
          simp [h_p'']
        · subst u₂ ; simp [h_p'']
      case unknown.known u uid =>
        split at h_p' <;> rename_i h_p'' <;> simp at h_p'
        subst h_p'
        simp [h_p'']
    case action =>
      cases h_a : req.action <;> cases a'
      <;> simp [Partial.Value.subst, Partial.ResidualExpr.subst]
      <;> simp [h_a, Partial.UidOrUnknown.subst] at h_a'
      case known.known => exact h_a'
      case unknown.unknown u₁ u₂ =>
        split at h_a' <;> rename_i h_a'' <;> simp at h_a'
        · subst u₂ ; rename_i u₂
          simp [h_a'']
        · subst u₂ ; simp [h_a'']
      case unknown.known u uid =>
        split at h_a' <;> rename_i h_a'' <;> simp at h_a'
        subst h_a'
        simp [h_a'']
    case resource =>
      cases h_r : req.resource <;> cases r'
      <;> simp [Partial.Value.subst, Partial.ResidualExpr.subst]
      <;> simp [h_r, Partial.UidOrUnknown.subst] at h_r'
      case known.known => exact h_r'
      case unknown.unknown u₁ u₂ =>
        split at h_r' <;> rename_i h_r'' <;> simp at h_r'
        · subst u₂ ; rename_i u₂
          simp [h_r'']
        · subst u₂ ; simp [h_r'']
      case unknown.known u uid =>
        split at h_r' <;> rename_i h_r'' <;> simp at h_r'
        subst h_r'
        simp [h_r'']
    case context =>
      simp [Partial.Value.subst, Partial.ResidualExpr.subst, List.map_attach₂_snd, Map.mapOnValues]
  all_goals simp [Spec.Expr.substToPartialValue, Partial.Value.subst, Partial.ResidualExpr.subst]
  case and x₁ x₂ | or x₁ x₂ | binaryApp x₁ x₂ =>
    intro h_req
    exact And.intro (subst_substToPartialValue x₁ h_req) (subst_substToPartialValue x₂ h_req)
  case unaryApp x₁ | getAttr x₁ _ | hasAttr x₁ _ => exact subst_substToPartialValue x₁
  case ite x₁ x₂ x₃ =>
    intro h_req
    and_intros
    · exact subst_substToPartialValue x₁ h_req
    · exact subst_substToPartialValue x₂ h_req
    · exact subst_substToPartialValue x₃ h_req
  case set xs | call xs =>
    simp [List.map₁_eq_map]
    intro h_req
    apply List.map_congr
    intro x _
    simp only [Function.comp_apply]
    exact subst_substToPartialValue x h_req
  case record attrs =>
    simp [List.map_attach₂_snd]
    intro h_req
    apply List.map_congr
    intro (a, x) hx
    simp only [Function.comp_apply, Prod.mk.injEq, true_and]
    have := List.sizeOf_snd_lt_sizeOf_list hx
    exact subst_substToPartialValue x h_req
termination_by x
