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
import Cedar.Thm.TPE.Attrs
import Cedar.Thm.Validation
import Cedar.Thm.WellTyped.Residual

/-!
This file proves the central soundness property of `residualState`: what TPE
believes about the value a residual denotes is true of what that residual
actually evaluates to.

Everything TPE concludes about attribute access — `has`, `getAttr`, `getTag`, and
the folding of a partially-known record back into a value — is a corollary.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

/-! ### Bridging the concrete lookups to `find?` -/

/-- Reading an attribute of a concrete record succeeds exactly on its keys. -/
theorem getAttr_record_toOption {m : Map Attr Value} {a : Attr} {es : Entities} :
  (Spec.getAttr (.record m) a es).toOption = m.find? a
:= by
  simp only [Spec.getAttr, Spec.attrsOf, Except.bind_ok, Map.findOrErr]
  cases m.find? a <;> simp only [Except.toOption]

/-- Reading an attribute of an entity succeeds exactly on the keys it has, where
a missing entity has no attributes. -/
theorem getAttr_entity_toOption {uid : EntityUID} {a : Attr} {es : Entities} :
  (Spec.getAttr (.prim (.entityUID uid)) a es).toOption = (es.attrsOrEmpty uid).find? a
:= by
  simp only [Spec.getAttr, Spec.attrsOf, Entities.attrs, Entities.attrsOrEmpty,
    Map.findOrErr, bind, Except.bind]
  cases hf : es.find? uid with
  | none => simp only [Except.toOption, Map.find?_empty]
  | some d =>
    simp only
    cases d.attrs.find? a <;> simp only [Except.toOption]

/-- Reading a tag succeeds exactly on the tags the entity has. -/
theorem getTag_toOption {uid : EntityUID} {t : Tag} {es : Entities} :
  (Spec.getTag uid t es).toOption = (es.tagsOrEmpty uid).find? t
:= by
  simp only [Spec.getTag, Entities.tags, Entities.tagsOrEmpty, Map.findOrErr, bind, Except.bind]
  cases hf : es.find? uid with
  | none => simp only [Except.toOption, Map.find?_empty]
  | some d =>
    simp only
    cases d.tags.find? t <;> simp only [Except.toOption]

/-- `has` on a value whose attribute lookup succeeds is `true`. -/
theorem hasAttr_true_of_getAttr_some {v w : Value} {a : Attr} {es : Entities}
  (h : (Spec.getAttr v a es).toOption = .some w) :
  Spec.hasAttr v a es = .ok (.prim (.bool true))
:= by
  cases v with
  | prim p =>
    cases p with
    | entityUID uid =>
      rw [getAttr_entity_toOption] at h
      simp only [Spec.hasAttr, Spec.attrsOf, Except.bind_ok, Map.contains, h, Option.isSome_some]
    | _ => simp [Spec.getAttr, Spec.attrsOf, Except.toOption] at h
  | record m =>
    rw [getAttr_record_toOption] at h
    simp only [Spec.hasAttr, Spec.attrsOf, Except.bind_ok, Map.contains, h, Option.isSome_some]
  | _ => simp [Spec.getAttr, Spec.attrsOf, Except.toOption] at h

/-! ### `residualState` is sound -/

/--
What `residualState` reports about `r` is true of the value `r` evaluates to.

The proof is a structural recursion mirroring `residualState`: each shape it
looks through is discharged by the corresponding refinement fact (the partial
context refines the concrete one, the partial store refines the concrete one) or
by the schema (an attribute the partial data does not mention is recovered from
the declared type, which the concrete data conforms to).
-/
theorem residualState_sound
  {env : TypeEnv} {req : Request} {es : Entities}
  {preq : PartialRequest} {pes : PartialEntities}
  (h₂ : InstanceOfWellFormedEnvironment req es env)
  (h₄ : RequestAndEntitiesRefine req es preq pes)
  (r : Residual) (hwt : Residual.WellTyped env r) :
  AttrStateConsistent (residualState env preq pes r) ((r.evaluate req es).toOption)
:= by
  match r with
  | .val v ty =>
    simp only [residualState, Residual.evaluate, Except.toOption]
    exact .value
  | .var v ty =>
    cases v with
    | context =>
      simp only [residualState, Residual.evaluate, Except.toOption]
      cases hctx : preq.context with
      | none => exact .unknown
      | some pr =>
        have hcr := h₄.1.2.2.2.1
        rw [hctx] at hcr
        exact (PartialIsValid.some_inv.mp hcr).toAttrState
    | principal | action | resource =>
      simp only [residualState]
      exact .unknown
  | .getAttr r' a ty =>
    -- the interesting case: read `a` out of whatever we know about `r'`
    have hwt' : Residual.WellTyped env r' := by cases hwt <;> assumption
    have ih := residualState_sound h₂ h₄ r' hwt'
    simp only [residualState, attrStateAt]
    split
    case h_1 m hst =>
      -- `r'` is a fully concrete record
      rw [hst] at ih
      have hev := to_option_some.mp ih.value_inv
      simp only [Residual.evaluate, hev, Except.bind_ok, getAttr_record_toOption]
      cases hm : m.find? a with
      | none => simp only; exact .absent
      | some v => simp only; exact .value
    case h_2 uid hst =>
      -- `r'` is a concrete entity uid
      rw [hst] at ih
      have hev := to_option_some.mp ih.value_inv
      simp only [Residual.evaluate, hev, Except.bind_ok, getAttr_entity_toOption]
      exact entity_attr_consistent h₂ h₄.2
    case h_3 pr rty hst hty =>
      -- `r'` is a partially-known record; its type supplies the declared attrs
      rw [hst] at ih
      obtain ⟨m, hm, _, _, hcons⟩ := ih.partialRecord_inv
      have hev := to_option_some.mp hm
      have hinst : InstanceOfType env (.record m) (.record rty) := by
        have := residual_well_typed_is_sound h₂ hwt' hev
        rw [hty] at this
        exact this
      simp only [Residual.evaluate, hev, Except.bind_ok, getAttr_record_toOption]
      exact resolve_attr_consistent hinst hcons
    case h_4 => exact .unknown
  | .binaryApp op r₁ r₂ ty =>
    cases op with
    | getTag =>
      have hwt₁ : Residual.WellTyped env r₁ := by cases hwt; assumption
      have hwt₂ : Residual.WellTyped env r₂ := by cases hwt; assumption
      have ih₁ := residualState_sound h₂ h₄ r₁ hwt₁
      have ih₂ := residualState_sound h₂ h₄ r₂ hwt₂
      simp only [residualState]
      split
      case h_1 uid t hst₁ hst₂ =>
        rw [hst₁] at ih₁
        rw [hst₂] at ih₂
        have hev₁ := to_option_some.mp ih₁.value_inv
        have hev₂ := to_option_some.mp ih₂.value_inv
        simp only [Residual.evaluate, hev₁, hev₂, Except.bind_ok, Spec.apply₂, getTag_toOption]
        exact entity_tag_consistent h₄.2
      case h_2 => exact .unknown
    | _ => simp only [residualState]; exact .unknown
  | .ite _ _ _ _ | .and _ _ _ | .or _ _ _ | .unaryApp _ _ _
  | .hasAttr _ _ _ | .set _ _ | .record _ _ | .call _ _ _ | .error _ =>
    simp only [residualState]
    exact .unknown

/--
Restated for `attrStateAt`: what TPE knows about attribute `a` of the value `r`
denotes is true of what reading that attribute produces.

Only `r`'s own well-typedness is needed — the type annotation on any enclosing
`getAttr` node plays no part, which is what lets `has` (whose result type is
`Bool`) use this too.
-/
theorem attrStateAt_sound
  {env : TypeEnv} {req : Request} {es : Entities}
  {preq : PartialRequest} {pes : PartialEntities}
  {r : Residual} {a : Attr}
  (h₂ : InstanceOfWellFormedEnvironment req es env)
  (h₄ : RequestAndEntitiesRefine req es preq pes)
  (hwt : Residual.WellTyped env r) :
  AttrStateConsistent (attrStateAt env preq pes r a)
    ((Except.bind (r.evaluate req es) (Spec.getAttr · a es)).toOption)
:= by
  have ih := residualState_sound h₂ h₄ r hwt
  simp only [attrStateAt]
  split
  case h_1 m hst =>
    rw [hst] at ih
    have hev := to_option_some.mp ih.value_inv
    simp only [hev, Except.bind, getAttr_record_toOption]
    cases hm : m.find? a with
    | none => simp only; exact .absent
    | some v => simp only; exact .value
  case h_2 uid hst =>
    rw [hst] at ih
    have hev := to_option_some.mp ih.value_inv
    simp only [hev, Except.bind, getAttr_entity_toOption]
    exact entity_attr_consistent h₂ h₄.2
  case h_3 pr rty hst hty =>
    rw [hst] at ih
    obtain ⟨m, hm, _, _, hcons⟩ := ih.partialRecord_inv
    have hev := to_option_some.mp hm
    have hinst : InstanceOfType env (.record m) (.record rty) := by
      have hi := residual_well_typed_is_sound h₂ hwt hev
      rw [hty] at hi
      exact hi
    simp only [hev, Except.bind, getAttr_record_toOption]
    exact resolve_attr_consistent hinst hcons
  case h_4 => exact .unknown

/-! ### The reduction is well typed -/

/--
Reducing a residual to what TPE knows about its value preserves well-typedness.

The value read out of the request data is well typed because it *is* the value
the residual evaluates to, and a well-typed residual evaluates to a value of its
type. Folding a partially-known record uses `as_values_eq` to identify the folded
record with the concrete one.
-/
theorem stateToResidual_well_typed
  {env : TypeEnv} {req : Request} {es : Entities}
  {s : AttrState} {ty : CedarType} {self : Residual}
  (h₂ : InstanceOfWellFormedEnvironment req es env)
  (hcons : AttrStateConsistent s ((self.evaluate req es).toOption))
  (hswt : Residual.WellTyped env self)
  (hsty : self.typeOf = ty) :
  Residual.WellTyped env (TPE.stateToResidual s ty self)
:= by
  cases s with
  | value v =>
    have hev := to_option_some.mp hcons.value_inv
    exact .val (hsty ▸ residual_well_typed_is_sound h₂ hswt hev)
  | absent => exact .error
  | present => exact hswt
  | unknown => exact hswt
  | partialRecord pr =>
    cases ty
    case record rty =>
      simp only [TPE.stateToResidual]
      cases hf : PartialRecord.asValues? pr rty with
      | none => simpa only [hf, Option.map_none, someOrSelf] using hswt
      | some m' =>
        simp only [Option.map_some, someOrSelf]
        obtain ⟨m, hm, hrwf, hmwf, hc⟩ := hcons.partialRecord_inv
        have hev := to_option_some.mp hm
        have hinst : InstanceOfType env (.record m) (.record rty) := by
          have hi := residual_well_typed_is_sound h₂ hswt hev
          rw [hsty] at hi
          exact hi
        rw [as_values_eq hrwf hmwf hinst hc hf]
        exact .val hinst
    all_goals simpa only [TPE.stateToResidual] using hswt

/-! ### The reduction is sound -/

/--
Reducing a residual to what TPE knows about its value does not change what it
evaluates to.
-/
theorem stateToResidual_sound
  {env : TypeEnv} {req : Request} {es : Entities}
  {s : AttrState} {ty : CedarType} {self : Residual}
  (h₂ : InstanceOfWellFormedEnvironment req es env)
  (hcons : AttrStateConsistent s ((self.evaluate req es).toOption))
  (hswt : Residual.WellTyped env self)
  (hsty : self.typeOf = ty) :
  ((TPE.stateToResidual s ty self).evaluate req es).toOption
    = ((self.evaluate req es).toOption)
:= by
  cases s with
  | value v =>
    simp only [TPE.stateToResidual, Residual.evaluate, Except.toOption]
    exact hcons.value_inv.symm
  | absent =>
    simp only [TPE.stateToResidual, Residual.evaluate, Except.toOption]
    exact hcons.absent_inv.symm
  | present => rfl
  | unknown => rfl
  | partialRecord pr =>
    cases ty
    case record rty =>
      simp only [TPE.stateToResidual]
      cases hf : PartialRecord.asValues? pr rty with
      | none => simp only [Option.map_none, someOrSelf]
      | some m' =>
        simp only [Option.map_some, someOrSelf, Residual.evaluate, Except.toOption]
        obtain ⟨m, hm, hrwf, hmwf, hc⟩ := hcons.partialRecord_inv
        have hev := to_option_some.mp hm
        have hinst : InstanceOfType env (.record m) (.record rty) := by
          have hi := residual_well_typed_is_sound h₂ hswt hev
          rw [hsty] at hi
          exact hi
        rw [as_values_eq hrwf hmwf hinst hc hf]
        exact hm.symm
    all_goals simp only [TPE.stateToResidual]


/-! ### `has` follows the attribute's state -/

/--
TPE only forms an opinion about an attribute of a value it knows to be a record
or an entity, and `has` on those always succeeds, agreeing with whether the
attribute access itself would.
-/
theorem hasAttr_ok_of_state_known
  {env : TypeEnv} {req : Request} {es : Entities}
  {preq : PartialRequest} {pes : PartialEntities}
  {r : Residual} {a : Attr}
  (h₂ : InstanceOfWellFormedEnvironment req es env)
  (h₄ : RequestAndEntitiesRefine req es preq pes)
  (hwt : Residual.WellTyped env r)
  (hne : attrStateAt env preq pes r a ≠ .unknown) :
  ∃ v, r.evaluate req es = .ok v ∧
    Spec.hasAttr v a es = .ok (.prim (.bool ((Spec.getAttr v a es).toOption.isSome)))
:= by
  have hst := residualState_sound h₂ h₄ r hwt
  simp only [attrStateAt] at hne
  split at hne
  case h_1 m hs =>
    rw [hs] at hst
    refine ⟨.record m, to_option_some.mp hst.value_inv, ?_⟩
    simp only [Spec.hasAttr, Spec.attrsOf, Except.bind_ok, getAttr_record_toOption, Map.contains]
  case h_2 uid hs =>
    rw [hs] at hst
    refine ⟨.prim (.entityUID uid), to_option_some.mp hst.value_inv, ?_⟩
    simp only [Spec.hasAttr, Spec.attrsOf, Except.bind_ok, getAttr_entity_toOption, Map.contains]
  case h_3 pr rty hs hty =>
    rw [hs] at hst
    obtain ⟨m, hm, _, _, _⟩ := hst.partialRecord_inv
    refine ⟨.record m, to_option_some.mp hm, ?_⟩
    simp only [Spec.hasAttr, Spec.attrsOf, Except.bind_ok, getAttr_record_toOption, Map.contains]
  case h_4 => exact absurd rfl hne

/-- If TPE knows the attribute exists, `has` is `true`. -/
theorem hasAttr_true_of_state_exists
  {env : TypeEnv} {req : Request} {es : Entities}
  {preq : PartialRequest} {pes : PartialEntities}
  {r : Residual} {a : Attr}
  (h₂ : InstanceOfWellFormedEnvironment req es env)
  (h₄ : RequestAndEntitiesRefine req es preq pes)
  (hwt : Residual.WellTyped env r)
  (hex : (attrStateAt env preq pes r a).exists? = true) :
  ∃ v, r.evaluate req es = .ok v ∧ Spec.hasAttr v a es = .ok (.prim (.bool true))
:= by
  have hne : attrStateAt env preq pes r a ≠ .unknown := by
    intro hc; rw [hc] at hex; simp only [AttrState.exists?, Bool.false_eq_true] at hex
  obtain ⟨v, hev, hhas⟩ := hasAttr_ok_of_state_known h₂ h₄ hwt hne
  refine ⟨v, hev, ?_⟩
  have hcons := attrStateAt_sound (a := a) h₂ h₄ hwt
  obtain ⟨w, hw⟩ := AttrStateConsistent.exists_inv hex hcons
  simp only [hev, Except.bind] at hw
  simp only [hhas, hw, Option.isSome_some]

/-- If TPE knows the attribute is absent, `has` is `false`. -/
theorem hasAttr_false_of_state_absent
  {env : TypeEnv} {req : Request} {es : Entities}
  {preq : PartialRequest} {pes : PartialEntities}
  {r : Residual} {a : Attr}
  (h₂ : InstanceOfWellFormedEnvironment req es env)
  (h₄ : RequestAndEntitiesRefine req es preq pes)
  (hwt : Residual.WellTyped env r)
  (habs : attrStateAt env preq pes r a = .absent) :
  ∃ v, r.evaluate req es = .ok v ∧ Spec.hasAttr v a es = .ok (.prim (.bool false))
:= by
  have hne : attrStateAt env preq pes r a ≠ .unknown := by rw [habs]; simp
  obtain ⟨v, hev, hhas⟩ := hasAttr_ok_of_state_known h₂ h₄ hwt hne
  refine ⟨v, hev, ?_⟩
  have hcons := attrStateAt_sound (a := a) h₂ h₄ hwt
  rw [habs] at hcons
  have hw := hcons.absent_inv
  simp only [hev, Except.bind] at hw
  simp only [hhas, hw, Option.isSome_none]

end Cedar.Thm
