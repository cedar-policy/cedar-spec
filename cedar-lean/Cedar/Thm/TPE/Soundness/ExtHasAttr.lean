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
import Cedar.Thm.TPE.ErrorFree
import Cedar.Thm.TPE.WellTyped
import Cedar.Thm.Validation
import Cedar.Thm.WellTyped
import Cedar.Thm.Data.Control

import Cedar.Thm.TPE.Soundness.Basic
import Cedar.Thm.TPE.Soundness.HasAttr

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

/-- The reductions only ever decide `false`. -/
private theorem tryDecideHasResidual_false {env : TypeEnv} {r : Residual} {a : Attr} {v : Value}
  (hdec : TPE.tryDecideHasResidual env r a = .some v) : v = .prim (.bool false) := by
  unfold TPE.tryDecideHasResidual at hdec
  repeat' split at hdec
  all_goals simp_all

/-- A `has` of `false` ends the chain at `false`. -/
private theorem hasAttrs_loop_false_of_hasAttr
  {v : Value} {a : Attr} {rest : List Attr} {es : Entities}
  (hha : Spec.hasAttr v a es = .ok (.prim (.bool false))) :
  hasAttrs.loop v (a :: rest) es = .ok (.prim (.bool false)) := by
  simp only [Spec.hasAttr] at hha
  cases hao : Spec.attrsOf v (fun uid => .ok (es.attrsOrEmpty uid)) with
  | error => simp [hao] at hha
  | ok r =>
    simp only [hao, Except.bind_ok, Except.ok.injEq] at hha
    have hfind : r.find? a = .none := by
      cases hf : r.find? a with
      | none => rfl
      | some _ => simp [Map.contains, hf] at hha
    simp only [hasAttrs.loop, hao, hfind]

/--
A concrete entity whose type cannot declare `a` ends the chain at `false`, whether or not the
entity is in the store: absent, its attributes read as empty; present, store conformance keeps
it from carrying an undeclared attribute.
-/
private theorem attrsOrEmpty_find?_none_of_schema
  {env : TypeEnv} {req : Request} {es : Entities} {uid : EntityUID} {a : Attr} {v : Value}
  (hwf : InstanceOfWellFormedEnvironment req es env)
  (hdec : TPE.tryDecideHasResidual env (.val (.prim (.entityUID uid)) (.entity uid.ty)) a
    = .some v) :
  (es.attrsOrEmpty uid).find? a = .none := by
  unfold TPE.tryDecideHasResidual at hdec
  simp only [Residual.errorFree, Residual.typeOf, if_true] at hdec
  split at hdec
  case h_2 => simp at hdec
  case h_1 rty hsch =>
    split at hdec
    case isFalse => simp at hdec
    case isTrue hnone =>
      have hattr_none : rty.find? a = .none := Option.isNone_iff_eq_none.mp hnone
      cases hes : es.find? uid with
      | none =>
        simp only [Entities.attrsOrEmpty, hes]
        simp [Map.find?, Map.empty]
      | some edata =>
        have h_inst := well_typed_entity_attributes hwf hes hsch
        simp only [Entities.attrsOrEmpty, hes]
        exact absent_attribute_is_absent h_inst hattr_none

/-- The TPE extHasAttr loop is sound: evaluating its output equals the spec's hasAttrs.loop
    when the loop is called with a record value. -/
private theorem extHasAttr_loop_sound
  {env : TypeEnv} {m : Map Attr Value} {attrs : List Attr}
  {req : Request} {es : Entities}
  {preq : PartialRequest} {pes : PartialEntities}
  (hwf : InstanceOfWellFormedEnvironment req es env)
  (h_ref : RequestAndEntitiesRefine req es preq pes) :
  Except.toOption (hasAttrs.loop (.record m) attrs es) =
  Except.toOption ((TPE.extHasAttr.loop env m attrs pes (.bool .anyBool)).evaluate req es) := by
  induction attrs generalizing m with
  | nil =>
    simp [hasAttrs.loop, TPE.extHasAttr.loop, Residual.evaluate]
  | cons a rest ih =>
    unfold TPE.extHasAttr.loop
    cases rest with
    | nil =>
      simp [hasAttrs.loop, Spec.attrsOf, Residual.evaluate, Map.contains]
      cases m.find? a <;> simp [Except.toOption]
    | cons b rest' =>
      simp only [hasAttrs.loop, Spec.attrsOf]
      cases h₁ : m.find? a with
      | none => simp [Residual.evaluate, Except.toOption]
      | some next =>
        cases next with
        | record m_next =>
          simp only [TPE.attrsOf]
          exact ih
        | prim p =>
          cases p with
          | entityUID uid =>
            simp only [TPE.attrsOf]
            cases h₂ : pes.attrs uid with
            | some m' =>
              simp [PartialEntities.attrs, PartialEntities.get, Option.bind_eq_some_iff] at h₂
              rcases h₂ with ⟨h₃, h₄, h₅⟩
              simp [RequestAndEntitiesRefine, EntitiesRefine] at h_ref
              rcases h_ref with ⟨_, h₆⟩
              have h₇ := h₆ uid h₃ h₄
              rcases h₇ with ⟨_, h₈, h₉, _, _⟩
              simp only [h₅, PartialIsValid.some_inv] at h₉; subst h₉
              simp only [Entities.attrsOrEmpty, h₈]
              exact ih
            | none =>
              -- The subject is a known uid the partial store lacks; the schema may still
              -- rule out the next attribute.
              simp only [TPE.extHasAttr.tryDecide]
              cases hdec : TPE.tryDecideHasResidual env
                  (Residual.val (.prim (.entityUID uid)) (.entity uid.ty)) b with
              | some w =>
                have hfalse := tryDecideHasResidual_false hdec
                subst hfalse
                have hfind := attrsOrEmpty_find?_none_of_schema (a := b) hwf hdec
                simp [hdec, hfind, List.head!, Residual.evaluate, Except.toOption]
              | none =>
                simp [hdec, Residual.evaluate, Spec.hasAttrs, List.head!, List.tail,
                  hasAttrs.loop, Spec.attrsOf]
          | _ =>
            simp [TPE.attrsOf,  Residual.evaluate, Except.toOption]
        | set _ =>
          simp [TPE.attrsOf, Residual.evaluate, Except.toOption]
        | ext _ =>
          simp [TPE.attrsOf, Residual.evaluate, Except.toOption]

theorem partial_evaluate_is_sound_ext_has_attr
{env : TypeEnv}
{x₁ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{attr : Attr}
{attrs : List Attr}
(hwf : InstanceOfWellFormedEnvironment req es env)
(hwt : Residual.WellTyped env x₁)
(h₄ : RequestAndEntitiesRefine req es preq pes)
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate env x₁ preq pes).evaluate req es)) :
  Except.toOption ((x₁.extHasAttr attr attrs (CedarType.bool BoolType.anyBool)).evaluate req es) =
  Except.toOption ((TPE.evaluate env (x₁.extHasAttr attr attrs (CedarType.bool BoolType.anyBool)) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.extHasAttr]
  split
  case _ h₁ =>
    simp [h₁, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    simp [Residual.evaluate, hᵢ₁, Except.toOption]
  split
  case _ h₁ =>
    simp [TPE.attrsOf] at h₁
    split at h₁
    case h_1 _ _ h₃ =>
      simp only [Option.some.injEq] at h₁; subst h₁
      simp only [h₃, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [Residual.evaluate, hᵢ₁, Spec.hasAttrs]
      exact extHasAttr_loop_sound hwf h₄
    case h_2 u₁ _ h₃ =>
      simp [h₃, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [PartialEntities.attrs, PartialEntities.get, Option.bind_eq_some_iff] at h₁
      rcases h₁ with ⟨x₅, h₉, h₁₀⟩
      have h₄' := h₄
      simp [RequestAndEntitiesRefine, EntitiesRefine] at h₄'
      rcases h₄' with ⟨_, h₅⟩
      rcases h₅ u₁ x₅ h₉ with ⟨x₆, h₇, h₈, _, _⟩
      simp only [h₁₀, PartialIsValid.some_inv] at h₈; subst h₈
      have h₁₁ : Except.toOption (hasAttrs.loop (.record x₆.attrs) (attr :: attrs) es) =
                 Except.toOption ((TPE.extHasAttr.loop env x₆.attrs (attr :: attrs) pes (.bool .anyBool)).evaluate req es) :=
        extHasAttr_loop_sound hwf h₄
      have h₁₂ : (x₁.extHasAttr attr attrs (.bool .anyBool)).evaluate req es =
                   hasAttrs.loop (.record x₆.attrs) (attr :: attrs) es := by
        simp [Residual.evaluate, hᵢ₁, Spec.hasAttrs, hasAttrs, hasAttrs.loop, Spec.attrsOf,
              Entities.attrsOrEmpty, h₇]
      rw [h₁₂]
      exact h₁₁
    case h_3 => cases h₁
  case _ =>
    -- attrsOf fails: the schema may still rule out the head attribute
    simp only [TPE.extHasAttr.tryDecide]
    cases hdec : TPE.tryDecideHasResidual env (TPE.evaluate env x₁ preq pes) attr with
    | some w =>
      have hfalse := tryDecideHasResidual_false hdec
      subst hfalse
      have hwt' := partial_eval_preserves_well_typed hwf h₄ hwt
      obtain ⟨v', hev, hha⟩ := try_decide_has_residual_sound hwf hwt' hdec
      have hx₁ : x₁.evaluate req es = .ok v' := to_option_some.mp (by rw [hᵢ₁, hev]; rfl)
      simp only [hdec, Residual.evaluate, hx₁, Except.bind_ok, Spec.hasAttrs,
        hasAttrs_loop_false_of_hasAttr hha, Except.toOption]
    | none =>
      simp only [hdec, Residual.evaluate]
      exact to_option_eq_do₁ (λ x => Spec.hasAttrs x attr attrs es) hᵢ₁

end Cedar.Thm
