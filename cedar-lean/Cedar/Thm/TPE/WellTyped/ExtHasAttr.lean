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
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.PreservesTypeOf
import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map

import Cedar.Thm.TPE.WellTyped.Basic
import Cedar.Thm.TPE.WellTyped.HasAttr
import Cedar.Thm.TPE.State
import Cedar.Thm.WellTyped.Expr.Typechecking

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

/--
The declared type `attrTypeOf` finds for an intermediate attribute of a valid
chain is an entity or record type from which the rest of the chain is valid.
-/
private theorem attrTypeOf_chain_valid {env : TypeEnv} {ty : CedarType} {a b : Attr}
  {bs : List Attr} {aty : CedarType}
  (hchain : ExtHasAttrChainValid env.ets ty (a :: b :: bs))
  (haty : TPE.attrTypeOf env ty a = .some aty) :
  ((∃ ety, aty = .entity ety) ∨ (∃ rty, aty = .record rty)) ∧
  ExtHasAttrChainValid env.ets aty (b :: bs)
:= by
  cases hchain with
  | cons_entity h₁ h₂ h₃ h₄ =>
    simp only [TPE.attrTypeOf, h₁] at haty
    rw [Option.map_some, Option.bind_some, lift_bool_types_record_eq_map_on_values,
      Data.Map.find?_mapOnValues, h₂] at haty
    simp only [Option.map_some, qualifiedType_liftBoolTypes_getType, h₃,
      CedarType.liftBoolTypes, Option.some.injEq] at haty
    subst haty
    exact ⟨.inl ⟨_, rfl⟩, h₄⟩
  | cons_record_from_entity h₁ h₂ h₃ h₄ =>
    simp only [TPE.attrTypeOf, h₁] at haty
    rw [Option.map_some, Option.bind_some, lift_bool_types_record_eq_map_on_values,
      Data.Map.find?_mapOnValues, h₂] at haty
    simp only [Option.map_some, qualifiedType_liftBoolTypes_getType, h₃,
      CedarType.liftBoolTypes, Option.some.injEq] at haty
    subst haty
    exact ⟨.inr ⟨_, rfl⟩, ExtHasAttrChainValid_liftBoolTypes_record h₄⟩
  | cons_not_in_schema_entity h₁ =>
    rcases h₁ with h₁ | h₁
    · simp [TPE.attrTypeOf, h₁] at haty
    · simp only [TPE.attrTypeOf, Option.bind_eq_some_iff, Option.map_eq_some_iff] at haty
      obtain ⟨_, ⟨rty, hrty, rfl⟩, qty, hq, _⟩ := haty
      rw [lift_bool_types_record_eq_map_on_values, Data.Map.find?_mapOnValues, h₁ rty hrty] at hq
      simp at hq
  | cons_entity_from_record h₁ h₂ h₃ =>
    simp only [TPE.attrTypeOf, h₁, Option.map_some, h₂, Option.some.injEq] at haty
    subst haty
    exact ⟨.inl ⟨_, rfl⟩, h₃⟩
  | cons_record_from_record h₁ h₂ h₃ =>
    simp only [TPE.attrTypeOf, h₁, Option.map_some, h₂, Option.some.injEq] at haty
    subst haty
    exact ⟨.inr ⟨_, rfl⟩, h₃⟩
  | cons_not_in_record h₁ =>
    simp [TPE.attrTypeOf, h₁] at haty

/-- Reading the intermediate attribute `attrTypeOf` finds is well typed. -/
private theorem attrTypeOf_getAttr_well_typed {env : TypeEnv} {r : Residual} {a : Attr}
  {aty : CedarType}
  (hwt : Residual.WellTyped env r)
  (haty : TPE.attrTypeOf env r.typeOf a = .some aty) :
  Residual.WellTyped env (.getAttr r a aty)
:= by
  simp only [TPE.attrTypeOf] at haty
  split at haty
  case h_1 rty hty => exact .getAttr_record hwt hty haty
  case h_2 ety hty =>
    simp only [Option.bind_eq_some_iff] at haty
    obtain ⟨rty, hrty, hfind⟩ := haty
    exact .getAttr_entity hwt hty hrty hfind
  case h_3 => simp at haty

/--
One step of the `extHasAttr` loop: if `r has a.b.bs` is well typed and `r.a`
has declared type `aty`, then the residual for `r.a has b.bs` is well typed.
-/
theorem extHasAttr_step_well_typed
  {env : TypeEnv} {req : Request} {es : Entities}
  {preq : PartialRequest} {pes : PartialEntities}
  {r : Residual} {a b : Attr} {bs : List Attr} {aty : CedarType}
  (hwf : InstanceOfWellFormedEnvironment req es env)
  (href : RequestAndEntitiesRefine req es preq pes)
  (hwt : Residual.WellTyped env (.extHasAttr r a (b :: bs) (.bool .anyBool)))
  (haty : TPE.attrTypeOf env r.typeOf a = .some aty) :
  Residual.WellTyped env (.getAttr r a aty) ∧
  Residual.WellTyped env (.extHasAttr
    (TPE.stateToResidual (attrStateAt env preq pes r a) aty (.getAttr r a aty))
    b bs (.bool .anyBool))
:= by
  have ⟨hr, hchain⟩ : Residual.WellTyped env r ∧
      ExtHasAttrChainValid env.ets r.typeOf (a :: b :: bs) := by
    cases hwt with
    | extHasAttr_entity h₁ h₂ h₃ => exact ⟨h₁, h₂ ▸ h₃⟩
    | extHasAttr_record h₁ h₂ h₃ => exact ⟨h₁, h₂ ▸ h₃⟩
  have hself := attrTypeOf_getAttr_well_typed hr haty
  have hcons : AttrStateConsistent (attrStateAt env preq pes r a)
      (((Residual.getAttr r a aty).evaluate req es).toOption) := by
    simpa only [Residual.evaluate, bind, Except.bind] using
      attrStateAt_sound (a := a) hwf href hr
  have hr' := stateToResidual_well_typed hwf hcons hself rfl
  have hty' := typeof_stateToResidual (s := attrStateAt env preq pes r a)
    (self := .getAttr r a aty) (ty := aty) rfl
  obtain ⟨hkind, hchain'⟩ := attrTypeOf_chain_valid hchain haty
  refine ⟨hself, ?_⟩
  rcases hkind with ⟨ety, hety⟩ | ⟨rty, hrty⟩
  · subst hety; exact .extHasAttr_entity hr' hty' hchain'
  · subst hrty; exact .extHasAttr_record hr' hty' hchain'

/-- The residual `extHasAttr` leaves for the partially evaluated operand is well typed. -/
theorem ext_has_attr_residual_well_typed
  {env : TypeEnv} {expr : Residual} {attr : Attr} {attrs : List Attr} {ty : CedarType}
  {preq : PartialRequest} {pes : PartialEntities}
  (h₁ : Residual.WellTyped env (TPE.evaluate env expr preq pes))
  (h₂ : Residual.WellTyped env (.extHasAttr expr attr attrs ty)) :
  Residual.WellTyped env
    (.extHasAttr (TPE.evaluate env expr preq pes) attr attrs (.bool .anyBool))
:= by
  cases h₂ with
  | extHasAttr_entity h₅ h₆ h₇ =>
    exact .extHasAttr_entity h₁ (by rw [partial_eval_preserves_typeof _ h₅ preq pes, h₆]) h₇
  | extHasAttr_record h₅ h₆ h₇ =>
    exact .extHasAttr_record h₁ (by rw [partial_eval_preserves_typeof _ h₅ preq pes, h₆]) h₇

/--
Each step of the `extHasAttr` loop keeps the residual it would leave behind well
typed, so whatever the loop produces is well typed.
-/
private theorem extHasAttr_loop_well_typed
  {env : TypeEnv} {req : Request} {es : Entities}
  {preq : PartialRequest} {pes : PartialEntities}
  {r : Residual} {a : Attr} {rest : List Attr}
  (hwf : InstanceOfWellFormedEnvironment req es env)
  (href : RequestAndEntitiesRefine req es preq pes)
  (hwt : Residual.WellTyped env (.extHasAttr r a rest (.bool .anyBool))) :
  Residual.WellTyped env (TPE.extHasAttr.loop env preq r a rest pes (.bool .anyBool))
:= by
  induction rest generalizing r a with
  | nil =>
    unfold TPE.extHasAttr.loop
    split
    · exact well_typed_bool
    · exact hwt
    · exact well_typed_bool
  | cons b bs ih =>
    unfold TPE.extHasAttr.loop
    split
    · exact well_typed_bool
    · exact hwt
    · dsimp only
      split
      · exact hwt
      · rename_i aty haty
        exact ih (extHasAttr_step_well_typed hwf href hwt haty).2

theorem partial_eval_well_typed_extHasAttr {env : TypeEnv} {expr : Residual} {attr : Attr} {attrs : List Attr} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate env expr preq pes) →
  PEWellTyped env (Residual.extHasAttr expr attr attrs ty) (TPE.evaluate env (Residual.extHasAttr expr attr attrs ty) preq pes) req preq es pes
:= by
  intros h₁ hwf href h₂
  have hwt' := ext_has_attr_residual_well_typed h₁ h₂
  have hty : ty = .bool .anyBool := by cases h₂ <;> rfl
  subst hty
  simp only [TPE.evaluate, TPE.extHasAttr]
  split
  · exact .error
  · exact extHasAttr_loop_well_typed hwf href hwt'

end Cedar.Thm
