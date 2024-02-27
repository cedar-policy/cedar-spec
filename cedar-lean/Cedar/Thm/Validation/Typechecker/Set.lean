/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Cedar.Thm.Data.List
import Cedar.Thm.Data.LT
import Cedar.Thm.Validation.Typechecker.Basic

/-!
This file proves that typechecking of `.set` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem lub_lub_fixed {ty₁ ty₂ ty₃ ty₄ : CedarType}
  (h₁ : (ty₁ ⊔ ty₂) = some ty₃)
  (h₂ : (ty₃ ⊔ ty₄) = some ty₄) :
  (ty₁ ⊔ ty₄) = some ty₄
:= by
  have h₃ := lub_left_subty h₁
  have h₄ := lub_left_subty h₂
  have h₅ := subty_trans h₃ h₄
  simp [subty] at h₅
  split at h₅ <;> simp at h₅ ; subst h₅
  assumption

theorem foldlM_of_lub_is_LUB {ty lubTy : CedarType } {tys : List CedarType}
  (h₁ : List.foldlM lub? ty tys = some lubTy) :
  (ty ⊔ lubTy) = some lubTy
:= by
  induction tys generalizing ty lubTy
  case nil =>
    simp [List.foldlM, pure] at h₁
    subst h₁
    exact lub_refl ty
  case cons hd tl ih =>
    simp [List.foldlM] at h₁
    cases h₂ : ty ⊔ hd <;>
    simp [h₂] at h₁
    rename_i lubTy'
    specialize ih h₁
    apply lub_lub_fixed h₂ ih

theorem foldlM_of_lub_assoc (ty₁ ty₂ : CedarType) (tys : List CedarType) :
  List.foldlM lub? ty₁ (ty₂ :: tys) =
  (do let ty₃ ← List.foldlM lub? ty₂ tys ; ty₁ ⊔ ty₃)
:= by
  apply List.foldlM_of_assoc
  intro x₁ x₂ x₃
  apply lub_assoc

theorem type_of_set_tail
  {x xhd : Expr } {xtl : List Expr} {c : Capabilities}
  {env : Environment} {ty hd : CedarType } {tl : List CedarType}
  (h₁ : (List.mapM₁ (xhd :: xtl) fun x => justType (typeOf x.val c env)) = Except.ok (hd :: tl))
  (h₂ : List.foldlM lub? hd tl = some ty)
  (h₃ : List.Mem x xtl) :
  ∃ ty', typeOf (Expr.set xtl) c env = Except.ok (.set ty', []) ∧
  (ty' ⊔ ty) = some ty
:= by
  cases xtl
  case nil =>
    have _ := List.not_mem_nil x
    contradiction
  case cons xhd' xtl' =>
    simp [typeOf]
    cases tl
    case nil =>
      simp [List.mapM₁, List.attach] at h₁
      simp [List.mapM_pmap_subtype (fun x => justType (typeOf x c env))] at h₁
      cases h₄ : justType (typeOf xhd c env) <;> simp [h₄] at h₁
      cases h₅ : justType (typeOf xhd' c env) <;> simp [h₅] at h₁
      cases h₆ : List.mapM (fun x => justType (typeOf x c env)) xtl' <;> simp [h₆] at h₁
      simp [pure, Except.pure] at h₁
    case cons hd' tl' =>
      simp [List.mapM₁] at h₁ ; unfold List.attach at h₁
      rw [List.mapM_pmap_subtype (fun x => justType (typeOf x c env))] at h₁
      have h₁ := List.mapM_head_tail h₁
      rw [←List.mapM₁_eq_mapM] at h₁
      simp [h₁, typeOfSet]
      cases h₄ : List.foldlM lub? hd' tl' <;>
      simp [h₄, err, ok]
      case none =>
        have h₅ := foldlM_of_lub_assoc hd hd' tl'
        rw [h₂, h₄] at h₅
        simp at h₅
      case some ty' =>
        have h₅ := foldlM_of_lub_assoc hd hd' tl'
        rw [h₂, h₄] at h₅
        simp at h₅ ; rw [eq_comm, lub_comm] at h₅
        have h₆ := lub_left_subty h₅
        simp [subty] at h₆
        split at h₆ <;> simp at h₆
        subst h₆
        assumption

theorem type_of_set_inversion {xs : List Expr} {c c' : Capabilities} {env : Environment} {sty : CedarType}
  (h₁ : typeOf (Expr.set xs) c env = Except.ok (sty, c')) :
  c' = ∅ ∧
  ∃ ty,
    sty = .set ty ∧
    ∀ xᵢ, xᵢ ∈ xs →
      ∃ tyᵢ cᵢ,
        typeOf xᵢ c env = Except.ok (tyᵢ, cᵢ) ∧
        (tyᵢ ⊔ ty) = .some ty
:= by
  simp [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp [h₂] at h₁
  simp [typeOfSet] at h₁
  split at h₁ <;> simp [ok, err] at h₁
  rename_i hd tl
  split at h₁ <;> simp at h₁
  rename_i ty h₃
  have ⟨hl₁, hr₁⟩ := h₁
  subst hl₁ hr₁
  simp only [List.empty_eq, CedarType.set.injEq, exists_and_right, exists_eq_left', true_and]
  intro x h₄
  cases h₄
  case head xtl =>
    simp [List.mapM₁, List.attach] at h₂
    rcases h₅ : justType (typeOf x c env) <;>
    simp [h₅] at h₂
    simp [List.mapM_pmap_subtype (fun x => justType (typeOf x c env))] at h₂
    rcases h₆ : List.mapM (fun x => justType (typeOf x c env)) xtl <;>
    simp [h₆, pure, Except.pure] at h₂
    have ⟨hl₂, hr₂⟩ := h₂ ; subst hl₂ hr₂
    rename_i hdty tlty
    simp [justType, Except.map] at h₅
    split at h₅ <;> simp at h₅
    rename_i res h₇
    exists hdty
    apply And.intro
    case left =>
      exists res.snd
      simp [←h₅, h₇]
    case right =>
      exact foldlM_of_lub_is_LUB h₃
  case tail xhd xtl h₄ =>
    have ⟨ty', h₅, h₆⟩ := type_of_set_tail h₂ h₃ h₄
    have h₇ := @type_of_set_inversion xtl c ∅ env (.set ty')
    simp [h₅] at h₇
    specialize h₇ x h₄
    have ⟨tyᵢ, h₇, h₈⟩ := h₇
    exists tyᵢ
    have ⟨cᵢ, h₇⟩ := h₇
    apply And.intro
    case left  => exists cᵢ
    case right => apply lub_lub_fixed h₈ h₆

theorem list_is_sound_implies_tail_is_sound {hd : Expr} {tl : List Expr}
  (h₁ : ∀ (xᵢ : Expr), xᵢ ∈ hd :: tl → TypeOfIsSound xᵢ) :
  ∀ (xᵢ : Expr), xᵢ ∈ tl → TypeOfIsSound xᵢ
:= by
  intro xᵢ h₂
  apply h₁
  simp [h₂]

theorem list_is_typed_implies_tail_is_typed {hd : Expr} {tl : List Expr} {c₁ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : ∀ (xᵢ : Expr), xᵢ ∈ hd :: tl → ∃ tyᵢ cᵢ, typeOf xᵢ c₁ env = Except.ok (tyᵢ, cᵢ) ∧ (tyᵢ ⊔ ty) = some ty) :
  ∀ (xᵢ : Expr), xᵢ ∈ tl → ∃ tyᵢ cᵢ, typeOf xᵢ c₁ env = Except.ok (tyᵢ, cᵢ) ∧ (tyᵢ ⊔ ty) = some ty
:= by
  intro xᵢ h₂
  apply h₁
  simp [h₂]

theorem type_of_set_is_sound_err {xs : List Expr} {c₁ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {err : Error}
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₄ : ∀ (xᵢ : Expr), xᵢ ∈ xs → ∃ tyᵢ cᵢ, typeOf xᵢ c₁ env = Except.ok (tyᵢ, cᵢ) ∧ (tyᵢ ⊔ ty) = some ty)
  (h₅ : (xs.mapM fun x => evaluate x request entities) = Except.error err) :
  err = Error.entityDoesNotExist ∨
  err = Error.extensionError ∨
  err = Error.arithBoundsError
:= by
  cases h₆ : xs
  case nil =>
    subst h₆
    simp [List.mapM₁, List.attach, pure, Except.pure] at h₅
  case cons hd tl =>
    simp [List.mapM₁, List.attach, h₆] at h₅
    have h₄ := h₄ hd
    simp only [h₆, List.mem_cons, true_or, forall_const] at h₄
    have ⟨tyᵢ, cᵢ, h₇, _⟩ := h₄
    have h₉ := ih hd ; simp [h₆, TypeOfIsSound] at h₉
    specialize (h₉ h₁ h₂ h₇) ; have ⟨_, v, h₉⟩ := h₉
    simp [EvaluatesTo] at h₉
    have ⟨h₉, _⟩ := h₉
    rcases h₉ with h₉ | h₉ | h₉ | h₉ <;>
    simp [h₉] at h₅ <;>
    try { simp [h₅] }
    subst h₆
    cases h₁₀ : List.mapM (fun x => evaluate x request entities) tl <;>
    simp [h₁₀, pure, Except.pure] at h₅ ; rw [eq_comm] at h₅
    subst h₅
    apply @type_of_set_is_sound_err
      tl c₁ env ty request entities err
      (list_is_sound_implies_tail_is_sound ih)
      h₁ h₂
      (list_is_typed_implies_tail_is_typed h₄)
    exact h₁₀

theorem type_of_set_is_sound_ok { xs : List Expr } { c₁ : Capabilities } { env : Environment } { request : Request } { entities : Entities } { ty : CedarType } { v : Value } { vs : List Value }
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : ∀ (xᵢ : Expr), xᵢ ∈ xs → ∃ tyᵢ cᵢ, typeOf xᵢ c₁ env = Except.ok (tyᵢ, cᵢ) ∧ (tyᵢ ⊔ ty) = some ty)
  (h₄ : (xs.mapM fun x => evaluate x request entities) = Except.ok vs)
  (h₅ : v ∈ vs):
  InstanceOfType v ty
:= by
  cases xs
  case nil =>
    simp [List.mapM₁, List.attach, pure, Except.pure] at h₄
    subst h₄
    simp only [List.find?_nil, List.not_mem_nil] at h₅
  case cons hd tl =>
    simp [List.mapM₁, List.attach] at h₄
    cases h₇ : evaluate hd request entities <;>
    simp [h₇] at h₄
    rename_i vhd
    cases h₈ : List.mapM (fun x => evaluate x request entities) tl <;>
    simp [h₈, pure, Except.pure] at h₄
    rename_i vtl
    subst h₄
    cases h₅
    case head =>
      specialize h₃ hd
      simp only [List.mem_cons, true_or, forall_const] at h₃
      have ⟨tyᵢ, cᵢ, h₃, h₆⟩ := h₃
      specialize ih hd
      simp [TypeOfIsSound] at ih
      specialize ih h₁ h₂ h₃
      have ⟨_, v', ihl, ihr⟩ := ih
      simp [EvaluatesTo] at ihl
      rcases ihl with ihl | ihl | ihl | ihl <;>
      simp [ihl] at h₇
      subst h₇
      exact instance_of_lub_left h₆ ihr
    case tail h₉ =>
      apply @type_of_set_is_sound_ok
        tl c₁ env request entities ty v vtl
        (list_is_sound_implies_tail_is_sound ih)
        h₁ h₂
        (list_is_typed_implies_tail_is_typed h₃)
        _ h₉
      simp [List.mapM₁, List.attach, List.mapM_pmap_subtype (evaluate · request entities), h₈]

theorem type_of_set_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {sty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.set xs) c₁ env = Except.ok (sty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.set xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.set xs) request entities v ∧ InstanceOfType v sty
:= by
  have ⟨h₆, ty, h₄, h₅⟩ := type_of_set_inversion h₃
  subst h₆ h₄
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    simp [EvaluatesTo, evaluate, List.mapM₁, List.attach, List.mapM_pmap_subtype (evaluate · request entities)]
    cases h₆ : xs.mapM fun x => evaluate x request entities <;>
    simp [h₆]
    case error err =>
      simp [type_is_inhabited]
      exact type_of_set_is_sound_err ih h₁ h₂ h₅ h₆
    case ok vs =>
      apply InstanceOfType.instance_of_set
      intro v h₇
      rw [←Set.make_mem] at h₇
      exact type_of_set_is_sound_ok ih h₁ h₂ h₅ h₆ h₇

end Cedar.Thm
