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
import Cedar.Thm.Validation
import Cedar.Spec

namespace Cedar.Thm

open Cedar.Validation
open Cedar.Thm
open Cedar.Spec

theorem well_typed_is_sound_call
{v : Value}
{request : Request}
{entities : Entities}
{xfn : ExtFun}
{args : List TypedExpr}
{ty : CedarType}
(h₁ : xfn.WellTyped args ty)
(h₂ : evaluate (Expr.call xfn (args.map₁ λ x => x.val.toExpr)) request entities = Except.ok v) :
InstanceOfType v (TypedExpr.call xfn args ty).typeOf
:= by
  generalize hᵢ : ((args.map₁ λ x => x.val.toExpr).mapM₁ λ x => evaluate x.val request entities) = res₁
  simp only [evaluate] at h₂
  cases res₁ <;> simp [hᵢ] at h₂
  simp only [call, res, gt_iff_lt, ge_iff_le] at h₂
  simp only [TypedExpr.typeOf]
  split at h₂ <;>
  cases h₁ <;>
  try cases h₂ <;>
  try simp only [bool_is_instance_of_anyBool]
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.decimal v) .decimal := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.decimal v) .decimal this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.ipaddr v) .ipAddr := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.ipaddr v) .ipAddr this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.datetime v) .datetime := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.datetime v) .datetime this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.duration v) .duration := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.duration v) .duration this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.datetime v) .datetime := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.datetime v) .datetime this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.duration v) .duration := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.duration v) .duration this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.datetime v) .datetime := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.datetime v) .datetime this
    · cases h₂
  case _ =>
    rename_i dt _ _
    have : InstanceOfExtType (Ext.duration dt.toTime) .duration := by
      simp only [InstanceOfExtType]
    exact InstanceOfType.instance_of_ext (Ext.duration dt.toTime) .duration this

theorem typechecked_is_well_typed_after_lifting_call
{c₁ c₂ : Capabilities}
{env : Environment}
{ty : TypedExpr}
{request : Request}
{entities : Entities}
{xfn : ExtFun}
{args : List Expr}
(h₂ : RequestAndEntitiesMatchEnvironment env request entities)
(h₃ : typeOf (Expr.call xfn args) c₁ env = Except.ok (ty, c₂)) :
TypedExpr.WellTyped env ty.liftBoolTypes
:= by
    simp [typeOf] at h₃
    simp [List.mapM₁_eq_mapM (λ x => justType (typeOf x c₁ env))] at h₃
    generalize hᵢ : List.mapM (fun x => justType (typeOf x c₁ env)) args = res₁
    cases res₁
    case error => simp [hᵢ] at h₃
    case ok ls =>
      simp [hᵢ] at h₃
      simp [List.mapM_ok_iff_forall₂] at hᵢ
      simp [typeOfCall] at h₃
      split at h₃ <;>
      try simp [ok, do_ok] at h₃ <;>
      rcases h₃ with ⟨_, h₃₁, h₃₂⟩ <;>
      subst h₃₂ <;>
      simp [TypedExpr.liftBoolTypes]
      · apply TypedExpr.WellTyped.call
        · simp [List.map₁_eq_map]
          intro a h
          rcases List.forall₂_implies_all_right hᵢ a h with ⟨_, _, h₄⟩
          simp [justType, Except.map] at h₄
          split at h₄
          case _ => cases h₄
          case _ e _ _ v heq =>
            simp at h₄
            have : v = (v.fst, v.snd) := by rfl
            rw [this, h₄] at heq
            --exact typechecked_is_well_typed_after_lifting h₂ heq
            sorry
        · simp [typeOfConstructor] at h₃₁
          split at h₃₁
          · split at h₃₁
            · rename_i heq
              simp [ok] at h₃₁
              rcases h₃₁ with ⟨h₃₁, _⟩
              subst h₃₁
              simp [CedarType.liftBoolTypes, List.map₁_eq_map]
              cases hᵢ
              · rename_i heq₁
                cases heq₁
                rename_i heq₂
                simp [typeOf, typeOfLit, ok, justType, Except.map] at heq₂
                subst heq₂
                simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
                symm at heq
                exact ExtFun.WellTyped.decimal heq
            · simp [err] at h₃₁
          · simp [err] at h₃₁
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry

end Cedar.Thm
