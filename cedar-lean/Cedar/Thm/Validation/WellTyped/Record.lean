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
import Cedar.Thm
import Cedar.Spec

namespace Cedar.Thm

open Cedar.Validation
open Cedar.Thm
open Cedar.Spec

theorem well_typed_is_sound_set
{v : Value}
{env : Environment}
{request : Request}
{entities : Entities}
{rty : RecordType}
{m : List (Attr × TypedExpr)}
(h₁ : RequestAndEntitiesMatchEnvironment env request entities)
(h₂ : ∀ (k : Attr) (v : TypedExpr), (k, v) ∈ m → WellTypedIsSound v)
(h₃ : ∀ (k : Attr) (v : TypedExpr), (k, v) ∈ m → TypedExpr.WellTyped env v)
(h₄ : rty =
  Data.Map.make
    (List.map
      (λ x =>
        match x with
        | (a, ty) => (a, Qualified.required ty.typeOf))
      m))
(h₅ : (do
  let avs ←
  (List.map (fun x => (x.1.fst, x.1.snd.toExpr)) m.attach₂).mapM₂ fun x =>
  bindAttr x.1.fst (evaluate x.1.snd request entities)
  Except.ok (Value.record (Data.Map.make avs))) = Except.ok v) :
InstanceOfType v (TypedExpr.record m (CedarType.record rty)).typeOf
:= by
  simp only [do_ok] at h₅
  obtain ⟨r, h₅₁, h₅₂⟩ := h₅
  simp only [← h₅₂, TypedExpr.typeOf]
  rw [List.map_attach₂ (fun x : Attr × TypedExpr => (x.fst, x.snd.toExpr))] at h₅₁
  simp only [List.mapM₂, List.attach₂] at h₅₁
  simp only [List.mapM_pmap_subtype
      (fun (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd request entities))] at h₅₁
  simp only [bindAttr, bind_pure_comp, List.mapM_map, List.mapM_ok_iff_forall₂] at h₅₁


  have h₆ : ∀ (k : Attr), (Data.Map.make r).contains k → rty.contains k := by
    sorry

  have h₇ : ∀ (k : Attr) (v : Value) (qty : QualifiedType),
    (Data.Map.make r).find? k = some v → rty.find? k = some qty → InstanceOfType v qty.getType := by
    sorry

  have h₈ : ∀ (k : Attr) (qty : QualifiedType), rty.find? k = some qty →
    qty.isRequired → (Data.Map.make r).contains k := by
    sorry

  exact InstanceOfType.instance_of_record (Data.Map.make r) rty h₆ h₇ h₈

end Cedar.Thm
