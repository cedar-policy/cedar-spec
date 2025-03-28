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

import Cedar.Validation.TypedExpr
import Cedar.Thm.Validation.WellTyped.Definition
import Cedar.Thm.Validation.Typechecker.Record
import Cedar.Spec

namespace Cedar.Thm

open Cedar.Validation
open Cedar.Thm
open Cedar.Spec

theorem attr_value_has_attrType
{request : Request}
{entities : Entities}
{m : List (Attr × TypedExpr)}
{r : List (Attr × Value)}
(h₁ : ∀ (k : Attr) (v : TypedExpr),
  (k, v) ∈ m → ∀ (v_1 : Value), evaluate v.toExpr request entities = Except.ok v_1 → InstanceOfType v_1 v.typeOf)
(h₃ : List.Forall₂ (λ x y => Prod.mk x.fst <$> evaluate x.snd.toExpr request entities = Except.ok y) m r) :
List.Forall₂ (λ x y => x.fst = y.fst ∧ InstanceOfType x.snd (Qualified.getType y.snd)) r (List.map
      (fun x =>
        match x with
        | (a, ty) => (a, Qualified.required ty.typeOf))
      m)
:= by
  cases h₃
  case nil => simp only [List.map_nil, List.Forall₂.nil]
  case cons at₁ av at₂ lv hᵢ₃ hᵢ₄ =>
    have h : (at₁.fst, at₁.snd) ∈ at₁ :: at₂ := by
        simp only [List.mem_cons, true_or]
    generalize hᵢ₅ : evaluate at₁.snd.toExpr request entities = res
    cases res
    case error => simp only [hᵢ₅, Except.map_error, reduceCtorEq] at hᵢ₃
    case ok v =>
      simp only [hᵢ₅, Except.map_ok, Except.ok.injEq] at hᵢ₃
      have hᵢ := attr_value_has_attrType (λ k v h => h₁ k v (List.mem_cons_of_mem at₁ h)) hᵢ₄
      have : av = (av.fst, av.snd) := by rfl
      rw [this] at hᵢ₃
      clear this
      simp only [Prod.mk.injEq] at hᵢ₃
      obtain ⟨hᵢ₃₁, hᵢ₃₂⟩ := hᵢ₃
      apply List.Forall₂.cons
      apply And.intro
      · simp only
        symm
        exact hᵢ₃₁
      · simp [Qualified.getType]
        have h₆ := h₁ at₁.fst at₁.snd
        simp at h₆
        specialize h₆ v hᵢ₅
        rw [hᵢ₃₂] at h₆
        exact h₆
      · exact hᵢ

theorem well_typed_is_sound_record
{v : Value}
{request : Request}
{entities : Entities}
{m : List (Attr × TypedExpr)}
{rty : RecordType}
(h₁ : ∀ (k : Attr) (v : TypedExpr),
  (k, v) ∈ m → ∀ (v_1 : Value), evaluate v.toExpr request entities = Except.ok v_1 → InstanceOfType v_1 v.typeOf)
(h₂ : rty =
  Data.Map.make
    (List.map
      (fun x =>
        match x with
        | (a, ty) => (a, Qualified.required ty.typeOf))
      m))
(h₃ : evaluate (Expr.record (List.map (fun x => (x.1.fst, x.1.snd.toExpr)) m.attach₂)) request entities = Except.ok v) :
  InstanceOfType v (TypedExpr.record m (CedarType.record rty)).typeOf
:= by
  simp only [evaluate, do_ok] at h₃
  obtain ⟨r, h₄, h₅⟩ := h₃
  subst h₅
  rw [List.map_attach₂ (fun x : Attr × TypedExpr => (x.fst, x.snd.toExpr))] at h₄
  simp only [List.mapM₂, List.attach₂] at h₄
  simp only [List.mapM_pmap_subtype
      (fun (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd request entities))] at h₄
  simp only [bindAttr, bind_pure_comp, List.mapM_map, List.mapM_ok_iff_forall₂] at h₄
  let rty' := (List.map
      (fun x =>
        match x with
        | (a, ty) => (a, Qualified.required ty.typeOf))
      m)
  have h₆ : rty = Data.Map.make rty' := by
    simp only [h₂]
    rfl
  subst h₆
  have h₅ : List.Forall₂ AttrValueHasAttrType r rty' := by
    exact attr_value_has_attrType h₁ h₄
  simp [TypedExpr.typeOf]
  apply mk_vals_instance_of_mk_types
  let p := fun (v : Value) (qty : QualifiedType) => InstanceOfType v qty.getType
  have h₆ := List.canonicalize_preserves_forallᵥ p r rty'
  simp only [List.Forallᵥ] at h₆
  exact h₆ h₅

end Cedar.Thm
