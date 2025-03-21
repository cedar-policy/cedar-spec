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
import Cedar.Thm
import Cedar.Spec

namespace Cedar.Thm

open Cedar.Validation
open Cedar.Thm
open Cedar.Spec

theorem attr_value_has_attrType
{env : Environment}
{request : Request}
{entities : Entities}
{m : List (Attr × TypedExpr)}
{r : List (Attr × Value)}
{rty : List (Attr × QualifiedType)}
(h₁ : RequestAndEntitiesMatchEnvironment env request entities)
(h₂ : ∀ (k : Attr) (v : TypedExpr), (k, v) ∈ m → WellTypedIsSound v)
(h₃ : ∀ (k : Attr) (v : TypedExpr), (k, v) ∈ m → TypedExpr.WellTyped env v)
(h₄ : List.Forall₂ (λ x y => x.fst = y.fst ∧ x.snd.typeOf = Qualified.getType y.snd) m rty)
(h₅ : List.Forall₂ (λ x y => Prod.mk x.fst <$> evaluate x.snd.toExpr request entities = Except.ok y) m r) :
List.Forall₂ (λ x y => x.fst = y.fst ∧ InstanceOfType x.snd (Qualified.getType y.snd)) r rty
:= by
  cases h₄ <;> cases h₅
  case nil.nil => simp only [List.Forall₂.nil]
  case cons.cons at₁ aq₁ at₂ aq₂ hᵢ₁ hᵢ₂ av lv hᵢ₃ hᵢ₄ =>
    have h : (at₁.fst, at₁.snd) ∈ at₁ :: at₂ := by
        simp only [List.mem_cons, true_or]
    have h₂₁ : WellTypedIsSound at₁.snd := by
      exact h₂ at₁.fst at₁.snd h
    have h' : ∀ (k : Attr) (v : TypedExpr), (k, v) ∈ at₂ → (k, v) ∈ at₁ :: at₂ := by
      intro k v
      simp [List.mem_cons_of_mem]
      intro a
      right
      exact a
    have h₂₂ : ∀ (k : Attr) (v : TypedExpr), (k, v) ∈ at₂ → WellTypedIsSound v := by
      intro k v h
      exact h₂ k v (h' k v h)
    have h₃₁ : TypedExpr.WellTyped env at₁.snd := by
      exact h₃ at₁.fst at₁.snd h
    have h₃₂ : ∀ (k : Attr) (v : TypedExpr), (k, v) ∈ at₂ → TypedExpr.WellTyped env v := by
      intro k v h
      exact h₃ k v (h' k v h)
    generalize hᵢ₃' : evaluate at₁.snd.toExpr request entities = res
    cases res
    case error => simp only [hᵢ₃', Except.map_error, reduceCtorEq] at hᵢ₃
    case ok v =>
      simp only [hᵢ₃', Except.map_ok, Except.ok.injEq] at hᵢ₃
      simp only [WellTypedIsSound] at h₂₁
      replace h₂₁ := h₂₁ h₁ h₃₁ hᵢ₃'
      obtain ⟨hᵢ₁₁, hᵢ₁₂⟩ := hᵢ₁
      have hᵢ := attr_value_has_attrType h₁ h₂₂ h₃₂ hᵢ₂ hᵢ₄
      have h' : av = (av.fst, av.snd) := by rfl
      rw [h'] at hᵢ₃
      simp only [Prod.mk.injEq] at hᵢ₃
      obtain ⟨hᵢ₃₁, hᵢ₃₂⟩ := hᵢ₃
      have h : av.fst = aq₁.fst ∧ InstanceOfType av.snd (Qualified.getType aq₁.snd) := by
        rw [←hᵢ₁₁]
        simp only [hᵢ₃₁, true_and]
        simp only [hᵢ₃₂, hᵢ₁₂] at h₂₁
        exact h₂₁
      exact List.Forall₂.cons h hᵢ


theorem well_typed_is_sound_record
{v : Value}
{env : Environment}
{request : Request}
{entities : Entities}
{m : List (Attr × TypedExpr)}
{rty : List (Attr × QualifiedType)}
(h₁ : RequestAndEntitiesMatchEnvironment env request entities)
(h₂ : ∀ (k : Attr) (v : TypedExpr), (k, v) ∈ m → WellTypedIsSound v)
(h₃ : ∀ (k : Attr) (v : TypedExpr), (k, v) ∈ m → TypedExpr.WellTyped env v)
(h₄ : List.Forall₂ (λ x y => x.fst = y.fst ∧ x.snd.typeOf = Qualified.getType y.snd) m rty)
(h₅ : (do
  let avs ←
  (List.map (λ x => (x.1.fst, x.1.snd.toExpr)) m.attach₂).mapM₂ λ x =>
  bindAttr x.1.fst (evaluate x.1.snd request entities)
  Except.ok (Value.record (Data.Map.make avs))) = Except.ok v) :
InstanceOfType v (TypedExpr.record m (CedarType.record (Data.Map.make rty))).typeOf
:= by
  simp only [do_ok] at h₅
  obtain ⟨r, h₅₁, h₅₂⟩ := h₅
  subst h₅₂
  rw [List.map_attach₂ (fun x : Attr × TypedExpr => (x.fst, x.snd.toExpr))] at h₅₁
  simp only [List.mapM₂, List.attach₂] at h₅₁
  simp only [List.mapM_pmap_subtype
      (fun (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd request entities))] at h₅₁
  simp only [bindAttr, bind_pure_comp, List.mapM_map, List.mapM_ok_iff_forall₂] at h₅₁
  have h₅ : List.Forall₂ AttrValueHasAttrType r rty := by
    exact attr_value_has_attrType h₁ h₂ h₃ h₄ h₅₁
  simp [TypedExpr.typeOf]
  apply mk_vals_instance_of_mk_types
  let p := fun (v : Value) (qty : QualifiedType) => InstanceOfType v qty.getType
  have h₆ := List.canonicalize_preserves_forallᵥ p r rty
  simp only [List.Forallᵥ] at h₆
  exact h₆ h₅

end Cedar.Thm
