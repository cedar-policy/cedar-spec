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

import Cedar.TPE
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.TPE.Input
import Cedar.Thm.Validation
import Cedar.Thm.WellTyped

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

theorem as_value_some {r : Residual} {v : Value} :
  r.asValue = .some v → (∃ ty, r = .val v ty)
:= by
  intro h
  simp only [Residual.asValue] at h
  split at h <;> simp at h
  subst h
  simp only [Residual.val.injEq, true_and, exists_eq']

theorem listM_some_listM_ok {req₁ : Request} {req₂ : PartialRequest} {es₁ : Entities} {es₂ : PartialEntities} {ls : List TypedExpr} {xs : List Value}
(hᵢ₄ : ∀ (x : TypedExpr),
  x ∈ ls →
    ∀ {v : Value} {ty : CedarType},
      TPE.evaluate x req₂ es₂ = Residual.val v ty → Spec.evaluate x.toExpr req₁ es₁ = Except.ok v)
(heq : List.mapM' (fun x => (TPE.evaluate x req₂ es₂).asValue) ls = some xs) :
  List.mapM' (fun x => Spec.evaluate x.toExpr req₁ es₁) ls = Except.ok xs
:= by
  induction ls generalizing xs
  case nil =>
    simp [List.mapM'] at heq
    simp [List.mapM']
    subst heq
    rfl
  case cons head tail hᵢ =>
    simp
    simp [Option.bind_eq_some] at heq
    rcases heq with ⟨v, h₁, vs, h₂, h₃⟩
    rcases as_value_some h₁ with ⟨_, h₁⟩
    have hᵢ₁ : head ∈ head :: tail := by
      simp only [List.mem_cons, true_or]
    have hᵢ₂ : ∀ x, x ∈ tail → x ∈ head :: tail := by
      intro x h
      simp ; right ; exact h
    have := hᵢ₄ head hᵢ₁ h₁
    simp [this]
    clear this
    specialize @hᵢ vs
    have : (∀ (x : TypedExpr),
    x ∈ tail →
      ∀ {v : Value} {ty : CedarType},
        TPE.evaluate x req₂ es₂ = Residual.val v ty → Spec.evaluate x.toExpr req₁ es₁ = Except.ok v) := by
      intro x h'
      specialize hᵢ₂ x h'
      exact hᵢ₄ x hᵢ₂
    specialize hᵢ this h₂
    simp [hᵢ]
    exact h₃

theorem anyM_any {es₁ : Entities} {es₂ : PartialEntities} {b : Bool} {uid : EntityUID} {uids : List EntityUID} (h : EntitiesAreConsistent es₁ es₂):
List.anyM (fun x => if uid = x then some true else Option.map (fun x_1 => x_1.contains x) (es₂.ancestors uid)) uids =
  some b →
  (uids.any fun x => uid == x || (es₁.ancestorsOrEmpty uid).contains x) = b
:= by
  induction uids generalizing b
  case nil => simp
  case cons head tail hᵢ =>
    intro h₁
    simp at h₁
    simp
    split at h₁
    case isTrue heq =>
      simp at h₁
      simp [heq]
      exact h₁
    case isFalse hneq =>
      simp [Option.bind] at h₁
      split at h₁ <;> simp at h₁
      rename_i heq
      simp at heq
      rcases heq with ⟨ancestors₂, heq₁, heq₂⟩
      simp [PartialEntities.ancestors, PartialEntities.get, Option.bind] at heq₁
      split at heq₁ <;> try cases heq₁
      rename_i data heq₃
      simp [EntitiesAreConsistent] at h
      specialize h uid data heq₃
      rcases h with ⟨e, h₂, _, h₃, _⟩
      split at h₁
      case _ =>
        simp at h₁
        subst h₁
        rw [heq₁] at h₃
        cases h₃
        rename_i heq₄
        simp [Entities.ancestorsOrEmpty, h₂, ←heq₄]
        left; right; exact heq₂
      case _ =>
        specialize hᵢ h₁
        rw [heq₁] at h₃
        cases h₃
        rename_i heq₄
        simp [Entities.ancestorsOrEmpty, h₂, ←heq₄]
        simp [Entities.ancestorsOrEmpty, h₂, ←heq₄] at hᵢ
        simp [heq₂, hᵢ, hneq]

theorem partial_evaluate_value_binary_app
  {x₁ x₂ : TypedExpr}
  {req₁ : Request}
  {es₁ : Entities}
  {req₂ : PartialRequest}
  {es₂ : PartialEntities}
  {env : Environment}
  {v : Value}
  {op₂ : BinaryOp}
  {ty ty₁: CedarType}
  (h₂ : IsConsistent req₁ es₁ req₂ es₂)
  (hᵢ₃ : BinaryOp.WellTyped env op₂ x₁ x₂ ty₁)
  (hᵢ₄ : ∀ {v : Value} {ty : CedarType},
    TPE.evaluate x₁ req₂ es₂ = Residual.val v ty → Spec.evaluate x₁.toExpr req₁ es₁ = Except.ok v)
  (hᵢ₅ : ∀ {v : Value} {ty : CedarType},
  TPE.evaluate x₂ req₂ es₂ = Residual.val v ty → Spec.evaluate x₂.toExpr req₁ es₁ = Except.ok v)
  (h₃ : TPE.apply₂ op₂ (TPE.evaluate x₁ req₂ es₂) (TPE.evaluate x₂ req₂ es₂) es₂ ty₁ = Residual.val v ty) :
  Spec.evaluate (Expr.binaryApp op₂ x₁.toExpr x₂.toExpr) req₁ es₁ = Except.ok v
:= by
  generalize h₁ᵢ : TPE.evaluate x₁ req₂ es₂ = res₁
  generalize h₂ᵢ : TPE.evaluate x₂ req₂ es₂ = res₂
  simp [h₁ᵢ, h₂ᵢ] at h₃
  unfold TPE.apply₂ at h₃
  split at h₃
  case _ heq₁ heq₂ =>
    split at h₃ <;>
    ( replace ⟨_, heq₁⟩ := as_value_some heq₁
      replace ⟨_, heq₂⟩ := as_value_some heq₂
      rw [heq₁] at h₁ᵢ
      rw [heq₂] at h₂ᵢ
      specialize hᵢ₄ h₁ᵢ
      specialize hᵢ₅ h₂ᵢ
      simp [Spec.evaluate, hᵢ₄, hᵢ₅, Spec.apply₂]
      try (simp at h₃; exact h₃.left)
      )
    case _ =>
      simp [intOrErr]
      simp [someOrError] at h₃
      split at h₃ <;> simp at h₃
      rename_i heq₃
      simp [Option.bind_eq_some] at heq₃
      rcases heq₃ with ⟨_, heq₃, heq₄⟩
      simp [heq₃]
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      exact heq₄
    case _ =>
      simp [intOrErr]
      simp [someOrError] at h₃
      split at h₃ <;> simp at h₃
      rename_i heq₃
      simp [Option.bind_eq_some] at heq₃
      rcases heq₃ with ⟨_, heq₃, heq₄⟩
      simp [heq₃]
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      exact heq₄
    case _ =>
      simp [intOrErr]
      simp [someOrError] at h₃
      split at h₃ <;> simp at h₃
      rename_i heq₃
      simp [Option.bind_eq_some] at heq₃
      rcases heq₃ with ⟨_, heq₃, heq₄⟩
      simp [heq₃]
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      exact heq₄
    case _ uid₁ _ _ _ =>
      simp [someOrSelf, TPE.inₑ, Option.map, Option.bind, apply₂.self] at h₃
      split at h₃ <;> simp at h₃
      rename_i heq₃
      split at heq₃ <;> cases heq₃
      rename_i heq₃
      rcases h₃ with ⟨h₃, _⟩ ; subst h₃
      split at heq₃
      case _ heq₄ =>
        simp at heq₃
        simp only [Spec.inₑ, heq₄, beq_self_eq_true, Bool.true_or, heq₃]
      case _ hneq =>
        split at heq₃ <;> cases heq₃
        rename_i heq₃
        simp [Spec.inₑ, Entities.ancestorsOrEmpty]
        simp [PartialEntities.ancestors, PartialEntities.get, Option.bind] at heq₃
        split at heq₃ <;> try cases heq₃
        rename_i data heq₄
        simp [IsConsistent, EntitiesAreConsistent] at h₂
        rcases h₂ with ⟨_, h₂⟩
        specialize h₂ uid₁ data heq₄
        rcases h₂ with ⟨_, h₂₁, _, h₂₂, _⟩
        rw [heq₃] at h₂₂
        cases h₂₂
        rename_i heq₅
        subst heq₅
        simp only [h₂₁, Bool.or_iff_right_iff_imp, beq_iff_eq, hneq, false_implies]
    case _ vs _ _ =>
      simp [someOrSelf, TPE.inₛ, Option.map, Option.bind, apply₂.self] at h₃
      split at h₃ <;> simp at h₃
      rename_i heq₃
      split at heq₃ <;> cases heq₃
      rename_i heq₃
      rcases h₃ with ⟨h₃, _⟩ ; subst h₃
      split at heq₃ <;> try cases heq₃
      rename_i vs' heq₄
      simp only at heq₃
      simp [Data.Set.toList] at heq₄
      simp [TPE.inₑ] at heq₃
      simp [Spec.inₛ, Data.Set.mapOrErr]
      rw [List.mapM_some_iff_forall₂] at heq₄
      have heq₅ : List.Forall₂ (fun x y => x.asEntityUID = .ok y) vs.elts vs' := by
        have : ∀ x y, (Except.toOption ∘ Value.asEntityUID) x = some y → x.asEntityUID = .ok y := by
          intro x y h
          simp [Except.toOption] at h
          split at h <;> cases h
          rename_i heq
          exact heq
        exact List.Forall₂.imp this heq₄
      rw [←List.mapM_ok_iff_forall₂] at heq₅
      simp [heq₅, Data.Set.make_any_iff_any, Spec.inₑ]
      simp [IsConsistent] at h₂
      -- TODO: replace it with applications of general lemmas
      exact anyM_any h₂.right heq₃
    case _ uid₁ _ _ _ =>
      simp [someOrSelf, Option.bind, apply₂.self] at h₃
      split at h₃ <;> simp at h₃
      rename_i heq₃
      split at heq₃ <;> cases heq₃
      rename_i heq₃
      simp [TPE.hasTag, PartialEntities.tags, PartialEntities.get, Option.bind_eq_some] at heq₃
      rcases heq₃ with ⟨data, heq₃₁, tags, heq₃₂, heq₃₃⟩
      simp [Spec.hasTag, Entities.tagsOrEmpty]
      simp [IsConsistent, EntitiesAreConsistent] at h₂
      rcases h₂ with ⟨_, h₂⟩
      specialize h₂ uid₁ data heq₃₁
      rcases h₂ with ⟨_, h₂₁, _, _, h₂₂⟩
      rw [heq₃₂] at h₂₂
      cases h₂₂
      rename_i heq₄
      simp [h₂₁, ←heq₄, heq₃₃]
      exact h₃.left
    case _ uid₁ _ _ _ =>
      simp [TPE.getTag] at h₃
      split at h₃ <;> simp [someOrError] at h₃
      split at h₃ <;> simp at h₃
      rename_i heq₃ _ _ _ _ heq₄
      simp [PartialEntities.tags, PartialEntities.get, Option.bind_eq_some] at heq₃
      rcases heq₃ with ⟨data, heq₃₁, heq₃₂⟩
      simp [IsConsistent, EntitiesAreConsistent] at h₂
      rcases h₂ with ⟨_, h₂⟩
      specialize h₂ uid₁ data heq₃₁
      rcases h₂ with ⟨_, h₂₁, _, _, h₂₂⟩
      rw [heq₃₂] at h₂₂
      cases h₂₂
      rename_i h₂₂
      simp [Spec.getTag, Data.Map.findOrErr, h₂₁, Entities.tags, ←h₂₂, heq₄]
      exact h₃.left
    case _ => simp only [reduceCtorEq] at h₃
  case _ =>
    split at h₃ <;> simp [apply₂.self] at h₃

theorem partial_evaluate_value
  {x : TypedExpr}
  {req₁ : Request}
  {es₁ : Entities}
  {req₂ : PartialRequest}
  {es₂ : PartialEntities}
  {env : Environment}
  {v : Value}
  {ty : CedarType} :
  RequestAndEntitiesMatchEnvironment env req₁ es₁ →
  TypedExpr.WellTyped env x →
  IsConsistent req₁ es₁ req₂ es₂ →
  TPE.evaluate x req₂ es₂ = .val v ty →
  Spec.evaluate x.toExpr req₁ es₁ = .ok v
:= by
  intro h₀ h₁ h₂ h₃
  induction h₁ generalizing v ty <;>
    simp [TypedExpr.toExpr] <;>
    simp [TPE.evaluate] at h₃
  case lit hᵢ₁ =>
    simp [Spec.evaluate]
    exact h₃.left
  case var hᵢ₁ =>
    cases hᵢ₁ <;>
    simp [Spec.evaluate] <;>
    simp [varₚ, varₚ.varₒ, someOrSelf, Option.bind] at h₃
    case action =>
      simp [IsConsistent, RequestIsConsistent] at h₂
      rcases h₂ with ⟨⟨_, h₂, _⟩, _⟩
      rw [h₂]
      exact h₃.left
    case principal =>
      split at h₃ <;>
      rename_i heq <;>
      split at heq <;>
      simp at heq <;>
      simp at h₃
      case _ heq₁ =>
        rcases h₃ with ⟨h₃, _⟩
        simp [IsConsistent, RequestIsConsistent] at h₂
        rcases h₂ with ⟨⟨h₂, _⟩, _⟩
        simp [heq₁] at h₂
        cases h₂
        rename_i heq₃
        simp [heq₃] at heq
        subst h₃
        exact heq
    case resource =>
      split at h₃ <;>
      rename_i heq <;>
      split at heq <;>
      simp at heq <;>
      simp at h₃
      case _ heq₁ =>
        rcases h₃ with ⟨h₃, _⟩
        simp [IsConsistent, RequestIsConsistent] at h₂
        rcases h₂ with ⟨⟨_, _, h₂, _⟩, _⟩
        simp [heq₁] at h₂
        cases h₂
        rename_i heq₃
        simp [heq₃] at heq
        subst h₃
        exact heq
    case context =>
      split at h₃ <;>
      simp at h₃
      case _ heq =>
        simp only [Option.map_eq_some'] at heq
        rcases heq with ⟨_, heq₁, heq₂⟩
        rcases h₃ with ⟨h₃, _⟩
        subst h₃
        simp [IsConsistent, RequestIsConsistent] at h₂
        rcases h₂ with ⟨⟨_, _, _, h₂⟩, _⟩
        simp [heq₁] at h₂
        cases h₂
        rename_i heq₃
        simp [heq₃] at heq₂
        exact heq₂
  case ite x₁ x₂ x₃ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ hᵢ₇ hᵢ₈ =>
    simp [TPE.ite] at h₃
    split at h₃ <;> try simp at h₃
    rename_i b _ heq
    cases b <;> simp at h₃ <;> simp [Spec.evaluate, hᵢ₆ heq, Result.as, Coe.coe, Value.asBool]
    · exact hᵢ₈ h₃
    · exact hᵢ₇ h₃
  case and x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    simp [TPE.and] at h₃
    split at h₃ <;> try simp at h₃
    case _ heq =>
      specialize hᵢ₅ heq
      specialize hᵢ₆ h₃
      simp [Spec.evaluate, hᵢ₅, Result.as, Coe.coe, Value.asBool, hᵢ₆]
      replace hᵢ₆ := well_typed_is_sound h₀ hᵢ₂ hᵢ₆
      simp [hᵢ₄] at hᵢ₆
      rcases instance_of_anyBool_is_bool hᵢ₆ with ⟨b, hᵢ₆⟩
      simp only [hᵢ₆, Except.map_ok]
    case _ heq =>
      specialize hᵢ₅ heq
      simp [Spec.evaluate, hᵢ₅, Result.as, Coe.coe, Value.asBool]
      exact h₃.left
    case _ heq _ _ _ =>
      specialize hᵢ₅ h₃
      have h₄ := well_typed_is_sound h₀ hᵢ₁ hᵢ₅
      simp [hᵢ₃] at h₄
      rcases instance_of_anyBool_is_bool h₄ with ⟨b, h₄⟩
      simp [Spec.evaluate, hᵢ₅, Result.as, Coe.coe, h₄, Value.asBool]
      specialize hᵢ₆ heq
      simp only [hᵢ₆, Except.map_ok, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq,
        Bool.true_eq, imp_self]
  case or x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    simp [TPE.or] at h₃
    split at h₃ <;> try simp at h₃
    case _ heq =>
      specialize hᵢ₅ heq
      simp [Spec.evaluate, hᵢ₅, Result.as, Coe.coe, Value.asBool]
      exact h₃.left
    case _ heq =>
      specialize hᵢ₅ heq
      specialize hᵢ₆ h₃
      simp [Spec.evaluate, hᵢ₅, Result.as, Coe.coe, Value.asBool, hᵢ₆]
      replace hᵢ₆ := well_typed_is_sound h₀ hᵢ₂ hᵢ₆
      simp [hᵢ₄] at hᵢ₆
      rcases instance_of_anyBool_is_bool hᵢ₆ with ⟨b, hᵢ₆⟩
      simp only [hᵢ₆, Except.map_ok]
    case _ heq _ _ _ =>
      specialize hᵢ₅ h₃
      have h₄ := well_typed_is_sound h₀ hᵢ₁ hᵢ₅
      simp [hᵢ₃] at h₄
      rcases instance_of_anyBool_is_bool h₄ with ⟨b, h₄⟩
      simp [Spec.evaluate, hᵢ₅, Result.as, Coe.coe, h₄, Value.asBool]
      specialize hᵢ₆ heq
      simp only [hᵢ₆, Except.map_ok, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq,
        Bool.false_eq, imp_self]
  case unaryApp op₁ x₁ _ hᵢ₁ hᵢ₂ hᵢ₃ =>
    simp [TPE.apply₁] at h₃
    split at h₃ <;> try simp at h₃
    split at h₃ <;> simp [someOrError] at h₃
    split at h₃ <;> simp at h₃
    simp [Spec.evaluate]
    rename_i heq _ _ _ _ heq₁
    simp [Residual.asValue] at heq
    split at heq <;> simp at heq
    rename_i heq₂
    specialize hᵢ₃ heq₂
    simp [hᵢ₃, heq]
    replace heq₁ := to_option_some heq₁
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    exact heq₁
  case binaryApp op₂ x₁ x₂ _ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ =>
    exact partial_evaluate_value_binary_app h₂ hᵢ₃ hᵢ₄ hᵢ₅ h₃
  case hasAttr_entity ety x₁ attr hᵢ₁ hᵢ₂ hᵢ₃ =>
    simp [TPE.hasAttr] at h₃
    split at h₃ <;> try simp at h₃
    split at h₃ <;> simp at h₃
    rename_i heq
    simp [TPE.attrsOf] at heq
    split at heq <;> try simp at heq
    case _ heq₁ =>
      specialize hᵢ₃ heq₁
      have heq₂ := well_typed_is_sound h₀ hᵢ₁ hᵢ₃
      rw [hᵢ₂] at heq₂
      cases heq₂
    case _ uid₁ _ heq₁ =>
      specialize hᵢ₃ heq₁
      simp [PartialEntities.attrs, PartialEntities.get, Option.bind_eq_some] at heq
      rcases heq with ⟨data, heq₂, heq₃⟩
      simp [IsConsistent, EntitiesAreConsistent] at h₂
      rcases h₂ with ⟨_, h₂⟩
      specialize h₂ uid₁ data heq₂
      rcases h₂ with ⟨_, h₂₁, h₂₂, _⟩
      rw [heq₃] at h₂₂
      cases h₂₂
      rename_i heq₄
      simp [Spec.evaluate, hᵢ₃, Spec.hasAttr, Spec.attrsOf, Entities.attrsOrEmpty, h₂₁, ←heq₄]
      exact h₃.left
  case hasAttr_record rty x₁ attr hᵢ₁ hᵢ₂ hᵢ₃ =>
    simp [TPE.hasAttr] at h₃
    split at h₃ <;> try simp at h₃
    split at h₃ <;> simp at h₃
    rename_i heq
    simp [TPE.attrsOf] at heq
    split at heq <;> try simp at heq
    case _ heq₁ =>
      specialize hᵢ₃ heq₁
      simp [Spec.evaluate, hᵢ₃, Spec.hasAttr, Spec.attrsOf, Entities.attrsOrEmpty]
      subst heq
      exact h₃.left
    case _ heq₁ =>
      specialize hᵢ₃ heq₁
      have heq₂ := well_typed_is_sound h₀ hᵢ₁ hᵢ₃
      rw [hᵢ₂] at heq₂
      cases heq₂
  case getAttr_entity ety rty x₁ attr _ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ =>
    simp [TPE.getAttr, someOrError] at h₃
    split at h₃ <;> try simp at h₃
    split at h₃ <;> try simp at h₃
    split at h₃ <;> simp at h₃
    rename_i heq _ _ _ _ heq₁
    simp [TPE.attrsOf] at heq
    split at heq <;> try cases heq
    case _ heq₂ =>
      specialize hᵢ₅ heq₂
      have heq₂ := well_typed_is_sound h₀ hᵢ₁ hᵢ₅
      rw [hᵢ₂] at heq₂
      cases heq₂
    case _ uid₁ _ heq₂ =>
      specialize hᵢ₅ heq₂
      simp [PartialEntities.attrs, PartialEntities.get, Option.bind_eq_some] at heq
      rcases heq with ⟨data, heq₃, heq₄⟩
      simp [IsConsistent, EntitiesAreConsistent] at h₂
      rcases h₂ with ⟨_, h₂⟩
      specialize h₂ uid₁ data heq₃
      rcases h₂ with ⟨_, h₂₁, h₂₂, _⟩
      rw [heq₄] at h₂₂
      cases h₂₂
      rename_i heq₅
      simp [Spec.evaluate, hᵢ₅, Spec.getAttr, Spec.attrsOf, Entities.attrs, Data.Map.findOrErr, h₂₁, ←heq₅, heq₁]
      exact h₃.left
  case getAttr_record rty x₁ attr _ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ =>
    simp [TPE.getAttr, someOrError] at h₃
    split at h₃ <;> try simp at h₃
    split at h₃ <;> try simp at h₃
    split at h₃ <;> simp at h₃
    rename_i heq _ _ _ _ heq₁
    simp [TPE.attrsOf] at heq
    split at heq <;> try cases heq
    case _ heq₂ =>
      specialize hᵢ₄ heq₂
      simp [Spec.evaluate, hᵢ₄, Spec.getAttr, Spec.attrsOf, Data.Map.findOrErr, heq₁]
      exact h₃.left
    case _ heq₂ =>
    specialize hᵢ₄ heq₂
    have heq₂ := well_typed_is_sound h₀ hᵢ₁ hᵢ₄
    rw [hᵢ₂] at heq₂
    cases heq₂
  case set ls _ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ =>
    simp [TPE.set] at h₃
    split at h₃ <;> try simp at h₃
    case _ xs heq =>
      simp [List.map₁_eq_map, Spec.evaluate, List.mapM₁_eq_mapM (fun x => Spec.evaluate x req₁ es₁) (List.map TypedExpr.toExpr ls), List.mapM_map, do_ok]
      exists xs
      rcases h₃ with ⟨h₃, _⟩
      simp only [h₃, and_true]
      simp [List.map₁_eq_map (fun x => TPE.evaluate x req₂ es₂) ls, List.mapM_map] at heq
      rw [←List.mapM'_eq_mapM] at heq
      rw [←List.mapM'_eq_mapM]
      -- TODO: replace it with applications of general lemmas
      exact listM_some_listM_ok hᵢ₄ heq
    case _ =>
      split at h₃ <;> simp at h₃
  case record rty m hᵢ₁ hᵢ₂ hᵢ₃ =>
    simp [record, List.map₁_eq_map (fun x => (x.fst, TPE.evaluate x.snd req₂ es₂)) m, List.mapM_map] at h₃
    split at h₃ <;> try simp at h₃
    case _ xs heq =>
      simp [Spec.evaluate, do_ok]
      exists xs
      rcases h₃ with ⟨h₃, _⟩
      simp only [h₃, and_true]
      -- repeat set
      sorry
    case _ =>
      split at h₃ <;> simp at h₃
  case call xfn args _ hᵢ₁ hᵢ₂ hᵢ₃ =>
    simp [List.map₁_eq_map (fun x => TPE.evaluate x req₂ es₂) args, TPE.call] at h₃
    split at h₃
    case _ xs heq =>
      simp [someOrError] at h₃
      split at h₃ <;> simp at h₃
      rename_i heq₁
      replace heq₁ := to_option_some heq₁
      simp [List.map₁_eq_map, Spec.evaluate, List.mapM₁_eq_mapM (fun x => Spec.evaluate x req₁ es₁) (List.map TypedExpr.toExpr args), List.mapM_map]
      -- repeat set
      sorry
    case _ =>
      split at h₃ <;> simp at h₃

end Cedar.Thm
