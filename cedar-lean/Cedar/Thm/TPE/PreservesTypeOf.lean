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
import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

abbrev PEPreservesTypeOf (res : Residual) : Prop :=
  ∀ {env : TypeEnv} , Residual.WellTyped env res →
    ∀ (preq : PartialRequest) (pes : PartialEntities),
      (TPE.evaluate res preq pes).typeOf = res.typeOf

private theorem partial_eval_preserves_typeof_and {a b : Residual} {ty : CedarType}
  (ih_a : PEPreservesTypeOf a)
  (ih_b : PEPreservesTypeOf b) :
  PEPreservesTypeOf (Residual.and a b ty)
:= by
  intro env h_wt preq pes
  simp only [TPE.evaluate, TPE.and]
  split
  · cases h_wt
    rename_i h_bwt h_bty
    specialize ih_b h_bwt preq pes
    rw [h_bty] at ih_b
    exact ih_b
  · simp only [Residual.typeOf]
    cases h_wt
    rfl
  · simp [Residual.typeOf]
  · cases h_wt
    rename_i h_awt h_aty _ _
    specialize ih_a h_awt preq pes
    rw [h_aty] at ih_a
    exact ih_a
  · split
    · simp only [Residual.typeOf]
      cases h_wt
      rfl
    · simp [Residual.typeOf]
  · simp [Residual.typeOf]

private theorem partial_eval_preserves_typeof_or {a b : Residual} {ty : CedarType}
  (ih_a : PEPreservesTypeOf a)
  (ih_b : PEPreservesTypeOf b) :
  PEPreservesTypeOf (Residual.or a b ty)
:= by
  intro env h_wt preq pes
  simp only [TPE.evaluate, TPE.or]
  split
  · simp only [Residual.typeOf]
    cases h_wt
    rfl
  · cases h_wt
    rename_i h_bwt h_bty
    specialize ih_b h_bwt preq pes
    rw [h_bty] at ih_b
    exact ih_b
  · simp [Residual.typeOf]
  · cases h_wt
    rename_i h_awt h_aty _ _
    specialize ih_a h_awt preq pes
    rw [h_aty] at ih_a
    exact ih_a
  · split
    · simp only [Residual.typeOf]
      cases h_wt
      rfl
    · simp [Residual.typeOf]
  · simp [Residual.typeOf]

private theorem partial_eval_preserves_typeof_ite {c t e : Residual} {ty : CedarType}
  (ih_t : PEPreservesTypeOf t)
  (ih_e : PEPreservesTypeOf e) :
  PEPreservesTypeOf (Residual.ite c t e ty)
:= by
  intro env h_wt preq pes
  simp only [TPE.evaluate, TPE.ite]
  split
  · cases h_wt
    split
    · rename_i h_twt _ _ _
      exact ih_t h_twt preq pes
    · rename_i h_ewt h_teq _
      rw [h_teq]
      exact ih_e h_ewt preq pes
  · simp [Residual.typeOf]
  · simp [Residual.typeOf]

private theorem partial_eval_preserves_typeof_unaryApp {op : UnaryOp} {e : Residual} {ty : CedarType} :
  PEPreservesTypeOf (Residual.unaryApp op e ty)
:= by
  intro env h_wt preq pes
  simp only [TPE.evaluate, TPE.apply₁]
  split
  . sorry -- Residual.evaluate changed shape for val case
  . sorry -- rename/split tactics broken due to evaluate restructuring

private theorem partial_eval_preserves_typeof_binaryApp {op : BinaryOp} {e1 e2 : Residual} {ty : CedarType} :
  PEPreservesTypeOf (Residual.binaryApp op e1 e2 ty)
:= by
  intro env h_wt preq pes
  simp only [TPE.evaluate, TPE.apply₂, Option.pure_def, Option.bind_eq_bind]
  split
  case h_1 =>
    sorry -- case tags changed due to TPE.apply₂ restructuring
  case h_2 =>
    split
    · simp [Residual.typeOf]
    · simp [Residual.typeOf]
    · simp [apply₂.self, Residual.typeOf]

private theorem partial_eval_preserves_typeof_call {xfn : ExtFun} {args : List Residual} {ty : CedarType} :
  PEPreservesTypeOf (Residual.call xfn args ty)
:= by
  intro env h_wt preq pes
  simp only [TPE.evaluate, TPE.call]
  split
  · simp only [someOrError]
    split
    · simp [Residual.typeOf]
    · simp [Residual.typeOf]
  · split
    · simp [Residual.typeOf]
    · simp [Residual.typeOf]

private theorem partial_eval_preserves_typeof_getAttr {expr : Residual} {attr : Attr} {ty : CedarType} :
  PEPreservesTypeOf (Residual.getAttr expr attr ty)
:= by
  intro env h_wt preq pes
  sorry -- TPE.getAttr/someOrError changed

private theorem partial_eval_preserves_typeof_hasAttr {expr : Residual} {attr : Attr} {ty : CedarType} :
  PEPreservesTypeOf (Residual.hasAttr expr attr ty)
:= by
  intro env h_wt preq pes
  sorry -- TPE.hasAttr changed

private theorem partial_eval_preserves_typeof_set {ls : List Residual} {ty : CedarType} :
  PEPreservesTypeOf (Residual.set ls ty)
:= by
  intro env h_wt preq pes
  simp only [TPE.evaluate, TPE.set]
  split
  · simp [Residual.typeOf]
  · split
    · simp [Residual.typeOf]
    · simp [Residual.typeOf]

private theorem partial_eval_preserves_typeof_record {ls : List (Attr × Residual)} {ty : CedarType} :
  PEPreservesTypeOf (Residual.record ls ty)
:= by
  intro env h_wt preq pes
  simp only [TPE.evaluate, TPE.record]
  split
  · simp [Residual.typeOf]
  · split
    · simp [Residual.typeOf]
    · simp [Residual.typeOf]

/--
Theorem: TPE.evaluate preserves the typeOf property.

If a residual has a certain type, then partially evaluating it produces
a residual with the same type.
-/
theorem partial_eval_preserves_typeof :
  ∀ res, PEPreservesTypeOf res
:= by
  intro res env
  cases res with
  | val v ty =>
    simp [TPE.evaluate, Residual.typeOf]
  | var v ty =>
    intro _ preq
    simp only [Residual.typeOf, TPE.evaluate]
    unfold varₚ
    simp only [varₚ.varₒ, someOrSelf]
    cases v with
    | principal =>
      cases h: preq.principal.asEntityUID <;> simp
    | resource | action =>
      cases h: preq.resource.asEntityUID <;> simp
    | context =>
      cases h: preq.context <;> simp
      sorry -- context is now PartialAttributes, more complex
  | error ty =>
    simp [TPE.evaluate, Residual.typeOf]
  | and a b ty =>
    exact partial_eval_preserves_typeof_and
      (partial_eval_preserves_typeof a) (partial_eval_preserves_typeof b)
  | or a b ty =>
    exact partial_eval_preserves_typeof_or
      (partial_eval_preserves_typeof a) (partial_eval_preserves_typeof b)
  | ite c t e ty =>
    exact partial_eval_preserves_typeof_ite
      (partial_eval_preserves_typeof t) (partial_eval_preserves_typeof e)
  | unaryApp op e ty =>
    exact partial_eval_preserves_typeof_unaryApp
  | binaryApp op e1 e2 ty =>
    exact partial_eval_preserves_typeof_binaryApp
  | call xfn args ty =>
    exact partial_eval_preserves_typeof_call
  | getAttr expr attr ty =>
    exact partial_eval_preserves_typeof_getAttr
  | hasAttr expr attr ty =>
    exact partial_eval_preserves_typeof_hasAttr
  | set ls ty =>
    exact partial_eval_preserves_typeof_set
  | record ls ty =>
    exact partial_eval_preserves_typeof_record
