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
import Cedar.Thm.TPE.State
import Cedar.Thm.TPE.WellTyped.ExtHasAttr

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

/-- A `has` of `true` on the last attribute ends the chain at `true`. -/
private theorem hasAttrs_loop_true_of_hasAttr
  {v : Value} {a : Attr} {es : Entities}
  (hha : Spec.hasAttr v a es = .ok (.prim (.bool true))) :
  hasAttrs.loop v [a] es = .ok (.prim (.bool true)) := by
  simp only [Spec.hasAttr] at hha
  cases hao : Spec.attrsOf v (fun uid => .ok (es.attrsOrEmpty uid)) with
  | error => simp [hao] at hha
  | ok r =>
    simp only [hao, Except.bind_ok, Except.ok.injEq] at hha
    cases hf : r.find? a with
    | none => simp [Map.contains, hf] at hha
    | some _ => simp only [hasAttrs.loop, hao, hf]

/-- Once attribute `a` of `v` is read as `w`, the rest of the chain continues from `w`. -/
private theorem hasAttrs_loop_of_getAttr
  {v w : Value} {a : Attr} {rest : List Attr} {es : Entities}
  (h : (Spec.getAttr v a es).toOption = .some w) :
  hasAttrs.loop v (a :: rest) es = hasAttrs.loop w rest es := by
  cases v with
  | prim p =>
    cases p with
    | entityUID uid =>
      rw [getAttr_entity_toOption] at h
      simp only [hasAttrs.loop, Spec.attrsOf, h]
    | _ => simp [Spec.getAttr, Spec.attrsOf, Except.toOption] at h
  | record m =>
    rw [getAttr_record_toOption] at h
    simp only [hasAttrs.loop, Spec.attrsOf, h]
  | _ => simp [Spec.getAttr, Spec.attrsOf, Except.toOption] at h

private theorem evaluate_extHasAttr_eq {r : Residual} {a : Attr} {l : List Attr}
  {ty : CedarType} {req : Request} {es : Entities} :
  (Residual.extHasAttr r a l ty).evaluate req es =
  Except.bind (r.evaluate req es) (λ v => Spec.hasAttrs v a l es) := by
  simp only [Residual.evaluate, bind]

/--
The `extHasAttr` loop is sound: each step it decides agrees with the concrete
`has`, and each attribute it reads through agrees with the concrete value.
-/
private theorem extHasAttr_loop_sound
  {env : TypeEnv} {req : Request} {es : Entities}
  {preq : PartialRequest} {pes : PartialEntities}
  {r : Residual} {a : Attr} {rest : List Attr}
  (hwf : InstanceOfWellFormedEnvironment req es env)
  (href : RequestAndEntitiesRefine req es preq pes)
  (hwt : Residual.WellTyped env (.extHasAttr r a rest (.bool .anyBool))) :
  Except.toOption ((TPE.extHasAttr.loop env preq r a rest pes (.bool .anyBool)).evaluate req es) =
  Except.toOption (Except.bind (r.evaluate req es) (λ v => Spec.hasAttrs v a rest es))
:= by
  induction rest generalizing r a with
  | nil =>
    have hr : Residual.WellTyped env r := by cases hwt <;> assumption
    unfold TPE.extHasAttr.loop
    split
    case h_1 hd =>
      unfold TPE.decideHasAttr at hd
      split at hd
      case h_1 w hdec =>
        have hfalse := tryDecideHasResidual_false hdec
        subst hfalse
        obtain ⟨v, hev, hha⟩ := try_decide_has_residual_sound hwf hr hdec
        simp [Residual.evaluate, hev, Except.bind, Spec.hasAttrs,
          hasAttrs_loop_false_of_hasAttr hha, Except.toOption]
      case h_2 =>
        split at hd <;> simp only [Option.some.injEq, Bool.true_eq_false, reduceCtorEq] at hd
        rename_i habs
        obtain ⟨v, hev, hha⟩ := hasAttr_false_of_state_absent hwf href hr habs
        simp [Residual.evaluate, hev, Except.bind, Spec.hasAttrs,
          hasAttrs_loop_false_of_hasAttr hha, Except.toOption]
    case h_2 => rw [evaluate_extHasAttr_eq]
    case h_3 hd =>
      unfold TPE.decideHasAttr at hd
      split at hd
      case h_1 => simp at hd
      case h_2 =>
        have hex : (attrStateAt env preq pes r a).exists? = true := by
          split at hd <;> simp_all [AttrState.exists?]
        obtain ⟨v, hev, hha⟩ := hasAttr_true_of_state_exists hwf href hr hex
        simp [Residual.evaluate, hev, Except.bind, Spec.hasAttrs,
          hasAttrs_loop_true_of_hasAttr hha, Except.toOption]
  | cons b bs ih =>
    have hr : Residual.WellTyped env r := by cases hwt <;> assumption
    unfold TPE.extHasAttr.loop
    split
    case h_1 hd =>
      unfold TPE.decideHasAttr at hd
      split at hd
      case h_1 w hdec =>
        have hfalse := tryDecideHasResidual_false hdec
        subst hfalse
        obtain ⟨v, hev, hha⟩ := try_decide_has_residual_sound hwf hr hdec
        simp [Residual.evaluate, hev, Except.bind, Spec.hasAttrs,
          hasAttrs_loop_false_of_hasAttr hha, Except.toOption]
      case h_2 =>
        split at hd <;> simp only [Option.some.injEq, Bool.true_eq_false, reduceCtorEq] at hd
        rename_i habs
        obtain ⟨v, hev, hha⟩ := hasAttr_false_of_state_absent hwf href hr habs
        simp [Residual.evaluate, hev, Except.bind, Spec.hasAttrs,
          hasAttrs_loop_false_of_hasAttr hha, Except.toOption]
    case h_2 => rw [evaluate_extHasAttr_eq]
    case h_3 hd =>
      dsimp only
      split
      case h_1 => rw [evaluate_extHasAttr_eq]
      case h_2 aty haty =>
        unfold TPE.decideHasAttr at hd
        split at hd
        case h_1 => simp at hd
        case h_2 =>
          have hex : (attrStateAt env preq pes r a).exists? = true := by
            split at hd <;> simp_all [AttrState.exists?]
          obtain ⟨v, hev, _⟩ := hasAttr_true_of_state_exists hwf href hr hex
          have hcons := attrStateAt_sound (a := a) hwf href hr
          obtain ⟨w, hw⟩ := AttrStateConsistent.exists_inv hex hcons
          simp only [hev, Except.bind] at hw
          obtain ⟨hself, hwt'⟩ := extHasAttr_step_well_typed hwf href hwt haty
          have hcons' : AttrStateConsistent (attrStateAt env preq pes r a)
              (((Residual.getAttr r a aty).evaluate req es).toOption) := by
            simpa only [Residual.evaluate, bind, Except.bind] using hcons
          have hsound := stateToResidual_sound (ty := aty) hwf hcons' hself rfl
          have hev' : (TPE.stateToResidual (attrStateAt env preq pes r a) aty
              (.getAttr r a aty)).evaluate req es = .ok w := by
            apply to_option_some.mp
            rw [hsound]
            simpa only [Residual.evaluate, hev, bind, Except.bind] using hw
          rw [@ih _ _ hwt', hev']
          simp only [hev, Except.bind, Spec.hasAttrs, hasAttrs_loop_of_getAttr hw]

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
(hwt : Residual.WellTyped env (.extHasAttr x₁ attr attrs (.bool .anyBool)))
(h₄ : RequestAndEntitiesRefine req es preq pes)
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate env x₁ preq pes).evaluate req es)) :
  Except.toOption ((x₁.extHasAttr attr attrs (CedarType.bool BoolType.anyBool)).evaluate req es) =
  Except.toOption ((TPE.evaluate env (x₁.extHasAttr attr attrs (CedarType.bool BoolType.anyBool)) preq pes).evaluate req es)
:= by
  have hx₁ : Residual.WellTyped env x₁ := by cases hwt <;> assumption
  have hwt' := ext_has_attr_residual_well_typed
    (partial_eval_preserves_well_typed hwf h₄ hx₁) hwt
  simp only [TPE.evaluate, TPE.extHasAttr]
  split
  case _ h₁ =>
    simp [h₁, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    simp [Residual.evaluate, hᵢ₁, Except.toOption]
  case _ =>
    rw [extHasAttr_loop_sound hwf h₄ hwt']
    simp only [Residual.evaluate]
    exact to_option_eq_do₁ (λ x => Spec.hasAttrs x attr attrs es) hᵢ₁

end Cedar.Thm
