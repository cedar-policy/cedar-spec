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

import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.GetAttr
import Cedar.Thm.Validation.Typechecker.HasAttr

/-!
This file proves that typechecking of `.extHasAttr` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

private theorem hasAttrs_loop_ok_is_bool {v₁ : Value} {attrs : List Attr} {es : Entities} {r : Value} :
  hasAttrs.loop v₁ attrs es = .ok r →
  ∃ b, r = Value.prim (.bool b)
:= by
  intro h₁
  induction attrs generalizing v₁ with
  | nil =>
    simp only [hasAttrs.loop, Except.ok.injEq] at h₁
    exact ⟨true, h₁.symm⟩
  | cons attr rest ih =>
    simp only [hasAttrs.loop] at h₁
    repeat split at h₁
    all_goals first
      | exact ih h₁
      | simp only [Except.ok.injEq] at h₁; exact ⟨_, h₁.symm⟩
      | simp at h₁


private theorem hasAttrs_ok_is_bool {v₁ : Value} {attr : Attr} {attrs : List Attr} {es : Entities} {r : Value} :
  hasAttrs v₁ attr attrs es = .ok r →
  ∃ b, r = Value.prim (.bool b)
:= by
  intro hok
  simp only [hasAttrs] at hok
  exact hasAttrs_loop_ok_is_bool hok

private theorem hasAttrs_loop_error_subset {v₁ : Value} {attrs : List Attr}
  {entities : Entities} {e : Error}
  (hha : hasAttrs.loop v₁ attrs entities = .error e) :
  e = .typeError
:= by
  induction attrs generalizing v₁ with
  | nil => simp [hasAttrs.loop] at hha
  | cons attr rest ih =>
    simp only [hasAttrs.loop] at hha
    repeat split at hha
    all_goals simp only [ExceptT.stM_eq, reduceCtorEq, Except.error.injEq] at hha
    . exact ih hha
    . exact hha.symm

private theorem hasAttrs_safe_errors {v₁ : Value} {a : Attr} {attrs : List Attr} {entities : Entities}
  {e : Error}
  (hha : hasAttrs v₁ a attrs entities = .error e) :
  e = .typeError
:= by
  simp only [hasAttrs] at hha
  exact hasAttrs_loop_error_subset hha

private theorem typeOfHasAttr_caps_subset {ty₁ : TypedExpr} {x₁ : Expr} {a : Attr} {c : Capabilities} {env : TypeEnv}
  {ty' : TypedExpr} {c' : Capabilities}
  (h : typeOfHasAttr ty₁ x₁ a c env = .ok (ty', c')) :
  c' = ∅ ∨ c' = Capabilities.singleton x₁ (.attr a)
:= by
  simp only [typeOfHasAttr] at h
  split at h
  case h_1 rty heq =>
    simp only [ok, bind, Except.bind] at h
    cases hattr : hasAttrInRecord rty x₁ a c true <;> simp [hattr] at h
    exact hasAttrInRecord_has_empty_or_singleton_capabilities (by rw [← h.2]; exact hattr)
  case h_2 ety heq =>
    split at h
    case h_1 rty' hety =>
      simp only [ok, bind, Except.bind] at h
      cases hattr : hasAttrInRecord rty' x₁ a c false <;> simp [hattr] at h
      exact hasAttrInRecord_has_empty_or_singleton_capabilities (by rw [← h.2]; exact hattr)
    case h_2 =>
      split at h
      · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
        exact Or.inl h.2.symm
      · simp [err] at h
  case h_3 => simp [err] at h

private theorem hasAttrs_loop_true_implies_find {v : Value} {a : Attr} {rest_attrs : List Attr} {es : Entities}
  (h : hasAttrs.loop v (a :: rest_attrs) es = .ok true) :
  ∃ m next, attrsOf v (fun uid => .ok (es.attrsOrEmpty uid)) = .ok m ∧
    m.find? a = .some next ∧
    (rest_attrs = [] ∨ hasAttrs.loop next rest_attrs es = .ok true) := by
  simp only [hasAttrs.loop] at h
  split at h
  · rename_i m hattrs
    split at h
    · rename_i h₁ h₂
      split at h
      · exact ⟨m, h₁, hattrs, h₂, Or.inl (List.isEmpty_iff.mp (by assumption))⟩
      · exact ⟨m, h₁, hattrs, h₂, Or.inr h⟩
    · simp at h
  · simp at h

private theorem getAttr_ok_of_attrsOf_find {v : Value} {a : Attr} {es : Entities}
  {m : Map Attr Value} {next : Value}
  (hattrs : attrsOf v (fun uid => .ok (es.attrsOrEmpty uid)) = .ok m)
  (hfind : m.find? a = .some next) :
  getAttr v a es = .ok next := by
  simp only [getAttr, attrsOf, bind, Except.bind, Map.findOrErr] at hattrs ⊢
  split at hattrs
  · simp only [Except.ok.injEq] at hattrs; subst hattrs
    simp [hfind]
  · simp only [Except.ok.injEq] at hattrs; subst hattrs
    simp only [Entities.attrs, Entities.attrsOrEmpty] at hfind ⊢
    split at hfind <;> rename_i h₂
    · simp only [h₂, Except.bind_ok, Map.findOrErr, hfind]
    · simp [Map.empty, Map.find?] at hfind
  · simp at hattrs

private theorem hasAttr_true_of_attrsOf_find {v : Value} {a : Attr} {es : Entities}
  {m : Map Attr Value} {next : Value}
  (hattrs : attrsOf v (fun uid => .ok (es.attrsOrEmpty uid)) = .ok m)
  (hfind : m.find? a = .some next) :
  hasAttr v a es = .ok true := by
  simp only [hasAttr, bind, Except.bind, hattrs]
  congr 1; congr 1; congr 1
  rw [Map.contains_iff_some_find?]
  exact ⟨next, hfind⟩

/--
Key lemma: if `typeOfGetAttr` succeeds, `InstanceOfType env v ty₁.typeOf`, and
`attrsOf v ... = .ok m` with `m.find? a = .some next`, then
`InstanceOfType env next tyNext.typeOf` where `tyNext` is the result type from `typeOfGetAttr`.
This connects the runtime attribute value to the declared schema type.
-/
private theorem instance_of_getAttr_type
  {ty₁ : TypedExpr} {x₁ : Expr} {a : Attr} {c : Capabilities} {env : TypeEnv}
  {tyNext : TypedExpr} {cga : Capabilities}
  {v : Value} {m : Map Attr Value} {next : Value}
  {request : Request} {entities : Entities}
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (hga : typeOfGetAttr ty₁ x₁ a c env = .ok (tyNext, cga))
  (hio : InstanceOfType env v ty₁.typeOf)
  (hattrs : attrsOf v (fun uid => .ok (entities.attrsOrEmpty uid)) = .ok m)
  (hfind : m.find? a = .some next)
  (heval : evaluate x₁ request entities = .ok v) :
  InstanceOfType env next tyNext.typeOf := by
  simp only [typeOfGetAttr, bind, Except.bind] at hga
  split at hga
  case h_1 rty hrty =>
    -- ty₁.typeOf = .record rty → v is a record
    rw [hrty] at hio
    have ⟨avs, hv⟩ := instance_of_record_type_is_record hio
    subst hv
    simp only [attrsOf, Except.ok.injEq] at hattrs; subst hattrs
    -- hga : (match getAttrInRecord ... with | error => error | ok v => ok ...) = .ok (tyNext, cga)
    -- Split on getAttrInRecord result inside hga
    split at hga
    case h_1 => simp at hga  -- error case: .error ≠ .ok
    case h_2 val_gir hgir =>
      -- getAttrInRecord succeeded
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hga
      obtain ⟨hty_eq, _⟩ := hga
      have htyof : tyNext.typeOf = val_gir.1 := by
        rw [← hty_eq]; simp [TypedExpr.typeOf]
      rw [htyof]
      -- Extract from getAttrInRecord that val_gir.1 is the type of attr a
      simp only [getAttrInRecord] at hgir
      split at hgir
      case h_1 aty hfind_rty =>
        -- Required: hgir : ok aty = .ok val_gir, so val_gir = (aty, ∅)
        have hval : val_gir = (aty, ∅) := by unfold ok at hgir; simp at hgir; exact hgir.symm
        rw [hval]
        exact instance_of_attribute_type hio hfind_rty rfl hfind
      case h_2 aty hfind_rty =>
        -- Optional: after if-split, same structure
        split at hgir
        · have hval : val_gir = (aty, ∅) := by unfold ok at hgir; simp at hgir; exact hgir.symm
          rw [hval]
          exact instance_of_attribute_type hio hfind_rty rfl hfind
        · simp [err] at hgir
      case h_3 => simp [err] at hgir
  case h_2 ety hety =>
    -- ty₁.typeOf = .entity ety → v is entity
    rw [hety] at hio
    have ⟨uid, huid_ty, hv⟩ := instance_of_entity_type_is_entity hio
    subst hv
    simp only [attrsOf, Except.ok.injEq] at hattrs; subst hattrs
    -- Schema lookup
    split at hga
    case h_1 rty hschema =>
      split at hga
      case h_1 => simp at hga  -- error case
      case h_2 val_gir hgir =>
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hga
        obtain ⟨hty_eq, _⟩ := hga
        have htyof : tyNext.typeOf = val_gir.1 := by
          rw [← hty_eq]; simp [TypedExpr.typeOf]
        rw [htyof]
        simp only [getAttrInRecord] at hgir
        split at hgir
        case h_1 aty hfind_rty =>
          have hval : val_gir = (aty, ∅) := by unfold ok at hgir; simp at hgir; exact hgir.symm
          rw [hval]
          subst huid_ty
          simp only [EntitySchema.attrs?] at hschema
          cases hfind_ent : entities.find? uid with
          | none =>
            exact absurd hfind (by simp [Entities.attrsOrEmpty, hfind_ent])
          | some d =>
            simp [Entities.attrsOrEmpty, hfind_ent] at hfind
            have hio_attrs := well_typed_entity_attributes h₂ hfind_ent hschema
            exact instance_of_attribute_type hio_attrs hfind_rty rfl hfind
        case h_2 aty hfind_rty =>
          split at hgir
          · have hval : val_gir = (aty, ∅) := by unfold ok at hgir; simp at hgir; exact hgir.symm
            rw [hval]
            subst huid_ty
            simp only [EntitySchema.attrs?] at hschema
            cases hfind_ent : entities.find? uid with
            | none =>
              exact absurd hfind (by simp [Entities.attrsOrEmpty, hfind_ent])
            | some d =>
              simp [Entities.attrsOrEmpty, hfind_ent] at hfind
              have hio_attrs := well_typed_entity_attributes h₂ hfind_ent hschema
              exact instance_of_attribute_type hio_attrs hfind_rty rfl hfind
          · simp [err] at hgir
        case h_3 => simp [err] at hgir
    case h_2 => simp [err] at hga
  case h_3 => simp [err] at hga

/--
If `typeOfHasAttr` succeeds, `attrsOf v` also succeeds (v is entity/record).
-/
private theorem attrsOf_ok_of_typeOfHasAttr
  {v₁ : Value} {ty₁ : TypedExpr} {x₁ : Expr} {a : Attr}
  {c : Capabilities} {env : TypeEnv} {entities : Entities}
  (hha₀ : ∃ r, typeOfHasAttr ty₁ x₁ a c env = .ok r)
  (hio₁ : InstanceOfType env v₁ ty₁.typeOf) :
  ∃ m, attrsOf v₁ (fun uid => .ok (entities.attrsOrEmpty uid)) = .ok m := by
  obtain ⟨r, h₀⟩ := hha₀
  simp only [typeOfHasAttr] at h₀
  split at h₀
  · rename_i _ h₁
    rw [h₁] at hio₁
    have ⟨x₁, h₂⟩ := instance_of_record_type_is_record hio₁
    subst h₂
    exact ⟨x₁, by simp [attrsOf]⟩
  · rename_i _ h₁
    split at h₀ <;> simp [err] at h₀
    all_goals (
      rw [h₁] at hio₁
      have ⟨x₁, _, h₂⟩ := instance_of_entity_type_is_entity hio₁
      subst h₂
      exact ⟨entities.attrsOrEmpty x₁, by simp [attrsOf]⟩)
  · simp [err] at h₀

/--
If `typeOfExtHasAttr` succeeds and `InstanceOfType env v ty₁.typeOf` holds,
then `hasAttrs.loop v attrs entities` cannot produce a type error.
The recursion of `typeOfExtHasAttr` mirrors `hasAttrs.loop`, so we can induct simultaneously.
-/
private theorem typeOfExtHasAttr_no_typeError
  {ty₁ : TypedExpr} {x₁ : Expr} {attrs : List Attr}
  {c : Capabilities} {env : TypeEnv}
  {v : Value} {request : Request} {entities : Entities}
  {res : BoolType × Capabilities}
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (hext : typeOfExtHasAttr ty₁ x₁ attrs c env = .ok res)
  (hio : InstanceOfType env v ty₁.typeOf)
  (h₁ : CapabilitiesInvariant c request entities)
  (heval : evaluate x₁ request entities = .ok v) :
  ∀ e, hasAttrs.loop v attrs entities ≠ .error e := by
  induction attrs generalizing ty₁ x₁ v c res with
  | nil =>
    -- hasAttrs.loop v [] = .ok true, never errors
    intro e he; simp [hasAttrs.loop] at he
  | cons a rest ih =>
    intro e he
    -- Unfold hasAttrs.loop
    simp only [hasAttrs.loop] at he
    split at he
    case h_1 m hattrs_ok =>
      split at he
      case h_1 next hfind =>
        split at he
        case isTrue => simp at he
        case isFalse hne =>
          cases rest with
          | nil => simp at hne
          | cons b rest' =>
            simp only [typeOfExtHasAttr, bind, Except.bind] at hext
            -- typeOfGetAttr must succeed
            cases hga : typeOfGetAttr ty₁ x₁ a c env with
            | error => simp [hga] at hext
            | ok val_ga =>
              simp only [hga] at hext
              obtain ⟨tyNext, _⟩ := val_ga
              -- typeOfHasAttr must succeed
              cases hha_ty : typeOfHasAttr ty₁ x₁ a c env with
              | error => simp [hha_ty] at hext
              | ok val_ha =>
                simp only [hha_ty] at hext
                obtain ⟨_, ci⟩ := val_ha
                -- Recursive typeOfExtHasAttr call
                cases hrec : typeOfExtHasAttr tyNext (Expr.getAttr x₁ a) (b :: rest') (c ∪ ci) env with
                | error => simp [hrec] at hext
                | ok val_rec =>
                  -- We have: InstanceOfType env next tyNext.typeOf
                  have hio_next : InstanceOfType env next tyNext.typeOf :=
                    instance_of_getAttr_type h₂ hga hio hattrs_ok hfind heval
                  -- evaluate (Expr.getAttr x₁ a) = .ok next
                  have heval_next : evaluate (Expr.getAttr x₁ a) request entities = .ok next := by
                    simp [evaluate, heval, getAttr_ok_of_attrsOf_find hattrs_ok hfind]
                  -- CapabilitiesInvariant (c ∪ ci) (from typeOfHasAttr caps being valid)
                  -- Actually we need hasAttr to hold for ci to be valid
                  -- But we know m.find? a = .some next, so hasAttr v a = .ok true
                  have hhasattr : hasAttr v a entities = .ok true :=
                    hasAttr_true_of_attrsOf_find hattrs_ok hfind
                  have hci_shape := typeOfHasAttr_caps_subset hha_ty
                  have hci_inv : CapabilitiesInvariant ci request entities := by
                    cases hci_shape with
                    | inl h => rw [h]; exact empty_capabilities_invariant request entities
                    | inr h =>
                      rw [h]
                      constructor
                      · intro x k hm
                        simp [Capabilities.singleton] at hm
                        obtain ⟨hx, hk⟩ := hm
                        subst hx; subst hk
                        simp [EvaluatesTo]
                        exact Or.inr (Or.inr (Or.inr (by simp [evaluate, heval, hhasattr])))
                      · intro x k hm
                        simp [Capabilities.singleton] at hm
                  have hc_ci_inv : CapabilitiesInvariant (c ∪ ci) request entities :=
                    capability_union_invariant h₁ hci_inv
                  -- Apply IH
                  exact ih hrec hio_next hc_ci_inv heval_next e he
      case h_2 =>
        -- m.find? a = .none → .ok false ≠ .error
        simp at he
    case h_2 hattrs_err =>
      -- attrsOf v failed. But InstanceOfType + typeOfExtHasAttr succeeding means
      -- ty₁.typeOf is entity or record, so v is entity/record, so attrsOf succeeds.
      -- Contradiction.
      exfalso
      -- typeOfExtHasAttr on (a :: rest) calls typeOfHasAttr or typeOfGetAttr which requires
      -- ty₁.typeOf to be entity or record
      have hattrsOf_ok : ∃ m, attrsOf v (fun uid => .ok (entities.attrsOrEmpty uid)) = .ok m := by
        cases rest with
        | nil =>
          -- typeOfExtHasAttr ty₁ x₁ [a] c env = typeOfHasAttr ty₁ x₁ a c env >>= ...
          simp only [typeOfExtHasAttr, bind, Except.bind] at hext
          cases hha : typeOfHasAttr ty₁ x₁ a c env with
          | error => simp [hha] at hext
          | ok val =>
            -- typeOfHasAttr succeeding means ty₁.typeOf is entity or record
            exact attrsOf_ok_of_typeOfHasAttr ⟨val, hha⟩ hio
        | cons b rest' =>
          -- typeOfExtHasAttr ty₁ x₁ (a :: b :: rest') starts with typeOfGetAttr
          simp only [typeOfExtHasAttr, bind, Except.bind] at hext
          cases hga : typeOfGetAttr ty₁ x₁ a c env with
          | error => simp [hga] at hext
          | ok val_ga =>
            -- typeOfGetAttr succeeding means ty₁.typeOf is entity or record
            simp only [typeOfGetAttr, bind, Except.bind] at hga
            split at hga
            · -- record
              rename_i rty hrty
              rw [hrty] at hio
              have ⟨avs, hv⟩ := instance_of_record_type_is_record hio
              subst hv
              exact ⟨avs, by simp [attrsOf]⟩
            · -- entity
              rename_i ety hety
              split at hga <;> simp [err] at hga
              rw [hety] at hio
              have ⟨euid, _, hv⟩ := instance_of_entity_type_is_entity hio
              subst hv
              exact ⟨entities.attrsOrEmpty euid, by simp [attrsOf]⟩
            · simp [err] at hga
      obtain ⟨m, hm⟩ := hattrsOf_ok
      simp [hm] at hattrs_err

/--
If `typeOfExtHasAttr` succeeds and `hasAttrs.loop` returns true,
then the output capabilities are invariant.
-/
private theorem typeOfExtHasAttr_gci
  {ty₁ : TypedExpr} {x₁ : Expr} {attrs : List Attr}
  {c : Capabilities} {env : TypeEnv}
  {v : Value} {request : Request} {entities : Entities}
  {res : BoolType × Capabilities}
  (hwf : InstanceOfWellFormedEnvironment request entities env)
  (hext : typeOfExtHasAttr ty₁ x₁ attrs c env = .ok res)
  (hloop : hasAttrs.loop v attrs entities = .ok true)
  (hio : InstanceOfType env v ty₁.typeOf)
  (hcap : CapabilitiesInvariant c request entities)
  (heval : evaluate x₁ request entities = .ok v) :
  CapabilitiesInvariant res.2 request entities := by
  induction attrs generalizing ty₁ x₁ v c res with
  | nil =>
    simp only [typeOfExtHasAttr, Except.ok.injEq] at hext
    rw [← hext]; simp
    exact empty_capabilities_invariant request entities
  | cons a rest ih =>
    -- hasAttrs.loop v (a :: rest) = .ok true implies attrsOf v succeeds and find? works
    have ⟨m, x₀, h₀, h₁, h₃⟩ := hasAttrs_loop_true_implies_find hloop
    -- hasAttr v a = .ok true
    have h₄ : hasAttr v a entities = .ok true :=
      hasAttr_true_of_attrsOf_find h₀ h₁
    cases rest with
    | nil =>
      -- typeOfExtHasAttr ty₁ x₁ [a] c env = typeOfHasAttr ty₁ x₁ a c env >>= ...
      simp only [typeOfExtHasAttr, bind, Except.bind] at hext
      cases h₅ : typeOfHasAttr ty₁ x₁ a c env with
      | error => simp [h₅] at hext
      | ok val_ha =>
        simp only [h₅] at hext
        -- Now handle the match on val_ha.fst.typeOf
        split at hext
        · -- .bool bty case
          simp only [Except.ok.injEq] at hext
          rw [← hext]
          have h₆ := typeOfHasAttr_caps_subset h₅
          cases h₆ with
          | inl h => rw [h]; exact empty_capabilities_invariant request entities
          | inr h =>
            rw [h]
            constructor <;> intro _ _ h₇ <;> simp [Capabilities.singleton] at h₇
            · obtain ⟨h₈, h₉⟩ := h₇; subst h₈ h₉
              simp only [EvaluatesTo, ExceptT.stM_eq]
              exact Or.inr (Or.inr (Or.inr (by simp [evaluate, heval, h₄])))
        · -- non-bool case
          simp only [Except.ok.injEq] at hext
          rw [← hext]
          have h₆ := typeOfHasAttr_caps_subset h₅
          cases h₆ with
          | inl h => rw [h]; exact empty_capabilities_invariant request entities
          | inr h =>
            rw [h]
            constructor <;> intro _ _ h₇ <;> simp [Capabilities.singleton] at h₇
            · obtain ⟨h₈, h₉⟩ := h₇; subst h₈ h₉
              simp only [EvaluatesTo, ExceptT.stM_eq]
              exact Or.inr (Or.inr (Or.inr (by simp [evaluate, heval, h₄])))
    | cons b rest' =>
      -- typeOfExtHasAttr ty₁ x₁ (a :: b :: rest') c env
      simp only [typeOfExtHasAttr, bind, Except.bind] at hext
      cases h₅ : typeOfGetAttr ty₁ x₁ a c env with
      | error => simp [h₅] at hext
      | ok val_ga =>
        simp only [h₅] at hext
        obtain ⟨tyNext, _⟩ := val_ga
        cases h₆ : typeOfHasAttr ty₁ x₁ a c env with
        | error => simp [h₆] at hext
        | ok val_ha =>
          simp only [h₆] at hext
          cases h₇ : typeOfExtHasAttr tyNext (Expr.getAttr x₁ a) (b :: rest') (c ∪ val_ha.2) env with
          | error => simp [h₇] at hext
          | ok val_rec =>
            simp only [h₇] at hext
            -- Both branches of the match on val_ha.fst.typeOf give caps = val_ha.2 ∪ val_rec.snd
            have hcaps : res.2 = val_ha.2 ∪ val_rec.2 := by
              revert hext; split
              · intro hext
                obtain ⟨_, h⟩ := Prod.mk.inj (Except.ok.inj hext)
                exact h.symm
              · intro hext
                obtain ⟨_, h⟩ := Prod.mk.inj (Except.ok.inj hext)
                exact h.symm
            rw [hcaps]
            -- val_ha.2 is valid (same as before)
            have h₉ : CapabilitiesInvariant val_ha.2 request entities := by
              cases typeOfHasAttr_caps_subset h₆ with
              | inl h => rw [h]; exact empty_capabilities_invariant request entities
              | inr h =>
                rw [h]
                constructor <;> intro _ _ h₇ <;> simp [Capabilities.singleton] at h₇
                · obtain ⟨h₈, h₉⟩ := h₇; subst h₈ h₉
                  simp [EvaluatesTo]
                  exact Or.inr (Or.inr (Or.inr (by simp [evaluate, heval, h₄])))
            -- val_rec.2 is valid by IH
            -- InstanceOfType env next tyNext.typeOf
            have hio_next : InstanceOfType env x₀ tyNext.typeOf :=
              instance_of_getAttr_type hwf h₅ hio h₀ h₁ heval
            -- evaluate (Expr.getAttr x₁ a) = .ok next
            have heval_next : evaluate (Expr.getAttr x₁ a) request entities = .ok x₀ := by
              simp [evaluate, heval, getAttr_ok_of_attrsOf_find h₀ h₁]
            -- CapabilitiesInvariant (c ∪ val_ha.2)
            have hc_ci_inv : CapabilitiesInvariant (c ∪ val_ha.2) request entities :=
              capability_union_invariant hcap h₉
            have hrec_inv : CapabilitiesInvariant val_rec.2 request entities := by
              have hloop_rest : hasAttrs.loop x₀ (b :: rest') entities = .ok true :=
                h₃.resolve_left (by simp)
              apply ih
              · exact h₇
              · exact hloop_rest
              · exact hio_next
              · exact hc_ci_inv
              · exact heval_next
            exact capability_union_invariant h₉ hrec_inv

/--
Helper: typeOfHasAttr returning .tt contradicts find? a = none at runtime.
This is used in both the nil and cons cases of typeOfExtHasAttr_bool_type_sound.
-/
private theorem typeOfHasAttr_tt_contradicts_find_none
  {ty₁ : TypedExpr} {x₁ : Expr} {a : Attr}
  {c : Capabilities} {env : TypeEnv}
  {v : Value} {request : Request} {entities : Entities}
  {val_ha : TypedExpr × Capabilities}
  {r : Map Attr Value}
  (hha : typeOfHasAttr ty₁ x₁ a c env = .ok val_ha)
  (heq_tt : val_ha.fst.typeOf = .bool .tt)
  (hio : InstanceOfType env v ty₁.typeOf)
  (hcap : CapabilitiesInvariant c request entities)
  (heval : evaluate x₁ request entities = .ok v)
  (hattrs : (attrsOf v (fun uid => .ok (entities.attrsOrEmpty uid))) = .ok r)
  (hfind_none : r.find? a = none) :
  False := by
  -- hasAttr v a entities = .ok false (from find? = none)
  have h_false : hasAttr v a entities = .ok false := by
    unfold hasAttr
    simp only [bind, Except.bind, hattrs, Map.contains]
    rw [hfind_none]; rfl
  -- Unfold typeOfHasAttr to extract why it returned .tt
  unfold typeOfHasAttr at hha
  split at hha
  case h_1 rty hrty =>
    -- Record case (knownToExist = true)
    simp only [ok, bind, Except.bind] at hha
    generalize hattr_rec : hasAttrInRecord rty x₁ a c true = res_rec at hha
    cases res_rec with
    | error => simp at hha
    | ok val =>
      simp only [Except.ok.injEq] at hha
      unfold hasAttrInRecord at hattr_rec
      split at hattr_rec
      case h_1 qty hqty_find =>
        simp only [ok] at hattr_rec
        split at hattr_rec
        case isTrue h_cond =>
          simp only [Except.ok.injEq] at hattr_rec
          have hio_rec : InstanceOfType env v (.record rty) := by rwa [hrty] at hio
          simp [Bool.or_eq_true, decide_eq_true_eq] at h_cond
          cases h_cond with
          | inl h_cap =>
            have h_cap_inv := hcap.1 x₁ a h_cap
            simp only [EvaluatesTo] at h_cap_inv
            rcases h_cap_inv with h | h | h | h
            all_goals simp [evaluate, heval, hasAttr, bind, Except.bind, hattrs,
              Map.contains, hfind_none] at h
          | inr h_req =>
            cases qty with
            | required aty =>
              have ⟨m, hm⟩ := instance_of_record_type_is_record hio_rec
              subst hm; simp [attrsOf] at hattrs; subst hattrs
              have h_present := required_attribute_is_present hio_rec hqty_find
              obtain ⟨_, h_some⟩ := h_present
              simp [hfind_none] at h_some
            | optional _ => simp [Qualified.isRequired] at h_req
        case isFalse =>
          simp only [Except.ok.injEq] at hattr_rec
          rw [← hattr_rec] at hha
          rw [← hha] at heq_tt; simp [TypedExpr.typeOf] at heq_tt
      case h_2 =>
        simp only [ok, Except.ok.injEq] at hattr_rec
        rw [← hattr_rec] at hha
        rw [← hha] at heq_tt; simp [TypedExpr.typeOf] at heq_tt
  case h_2 ety hety =>
    -- Entity case (knownToExist = false)
    split at hha
    case h_1 rty' hattrs_schema =>
      simp only [ok, bind, Except.bind] at hha
      generalize hattr_rec : hasAttrInRecord rty' x₁ a c false = res_rec at hha
      cases res_rec with
      | error => simp at hha
      | ok val =>
        simp only [Except.ok.injEq] at hha
        unfold hasAttrInRecord at hattr_rec
        split at hattr_rec
        case h_1 qty hqty =>
          simp only [ok] at hattr_rec
          split at hattr_rec
          case isTrue h_cond =>
            simp only [Except.ok.injEq] at hattr_rec
            -- For entity (knownToExist=false): only (x₁,.attr a) ∈ c gives .tt
            simp at h_cond
            have h_cap_inv := hcap.1 x₁ a h_cond
            simp only [EvaluatesTo] at h_cap_inv
            rcases h_cap_inv with h | h | h | h
            all_goals simp [evaluate, heval, hasAttr, bind, Except.bind, hattrs,
              Map.contains, hfind_none] at h
          case isFalse =>
            simp only [Except.ok.injEq] at hattr_rec
            rw [← hattr_rec] at hha
            rw [← hha] at heq_tt; simp [TypedExpr.typeOf] at heq_tt
        case h_2 =>
          simp only [ok, Except.ok.injEq] at hattr_rec
          rw [← hattr_rec] at hha
          rw [← hha] at heq_tt; simp [TypedExpr.typeOf] at heq_tt
    case h_2 =>
      split at hha
      · -- action type → .ff, contradicts .tt
        simp only [ok, Except.ok.injEq] at hha
        rw [← hha] at heq_tt; simp [TypedExpr.typeOf] at heq_tt
      · simp [err] at hha
  case h_3 => simp [err] at hha

/--
  The `BoolType` returned by `typeOfExtHasAttr` is precise: if the evaluation result
  is a boolean `b`, then `InstanceOfBoolType b bty`.
-/
private theorem typeOfExtHasAttr_bool_type_sound
  {ty₁ : TypedExpr} {x₁ : Expr} {attrs : List Attr}
  {c : Capabilities} {env : TypeEnv}
  {v : Value} {request : Request} {entities : Entities}
  {bty : BoolType} {caps : Capabilities} {b : Bool}
  (hwf : InstanceOfWellFormedEnvironment request entities env)
  (hext : typeOfExtHasAttr ty₁ x₁ attrs c env = .ok (bty, caps))
  (hio : InstanceOfType env v ty₁.typeOf)
  (hcap : CapabilitiesInvariant c request entities)
  (heval : evaluate x₁ request entities = .ok v)
  (hloop : hasAttrs.loop v attrs entities = .ok (.prim (.bool b))) :
  InstanceOfBoolType b bty := by
  induction attrs generalizing ty₁ x₁ v c bty caps with
  | nil =>
    simp only [typeOfExtHasAttr, Except.ok.injEq] at hext
    obtain ⟨hbty, _⟩ := Prod.mk.inj hext
    rw [← hbty]; simp [InstanceOfBoolType]
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [typeOfExtHasAttr, bind, Except.bind] at hext
      cases hha : typeOfHasAttr ty₁ x₁ a c env with
      | error => simp [hha] at hext
      | ok val_ha =>
        simp only [hha] at hext
        split at hext
        case h_1 bty' heq =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hext
          obtain ⟨hbty_eq, _⟩ := hext
          rw [← hbty_eq]
          simp only [hasAttrs.loop] at hloop
          split at hloop
          case h_2 => simp at hloop
          rename_i r hattrs
          split at hloop
          case h_1 next hfind =>
            simp at hloop; subst hloop
            cases bty' with
            | anyBool => simp [InstanceOfBoolType]
            | tt => simp [InstanceOfBoolType]
            | ff =>
              exfalso
              unfold typeOfHasAttr at hha
              split at hha
              case h_1 rty hrty =>
                simp only [ok, bind, Except.bind] at hha
                generalize hattr_rec : hasAttrInRecord rty x₁ a c true = res_rec at hha
                cases res_rec with
                | error => simp at hha
                | ok val =>
                  simp only [Except.ok.injEq] at hha
                  unfold hasAttrInRecord at hattr_rec
                  split at hattr_rec
                  case h_1 qty hqty =>
                    simp only [ok] at hattr_rec
                    split at hattr_rec
                    · simp only [Except.ok.injEq] at hattr_rec
                      rw [← hattr_rec] at hha
                      rw [← hha] at heq; simp [TypedExpr.typeOf] at heq
                    · simp only [Except.ok.injEq] at hattr_rec
                      rw [← hattr_rec] at hha
                      rw [← hha] at heq; simp [TypedExpr.typeOf] at heq
                  case h_2 =>
                    simp only [ok, Except.ok.injEq] at hattr_rec
                    have hio_rec : InstanceOfType env v (.record rty) := by rwa [hrty] at hio
                    have ⟨m, hm⟩ := instance_of_record_type_is_record hio_rec
                    subst hm
                    simp [attrsOf] at hattrs
                    subst hattrs
                    rename_i hfind_none
                    have h_absent := absent_attribute_is_absent hio_rec hfind_none
                    simp [h_absent] at hfind
              case h_2 ety hety =>
                -- Entity case
                split at hha
                case h_1 rty' hattrs_schema =>
                  simp only [ok, bind, Except.bind] at hha
                  generalize hattr_rec : hasAttrInRecord rty' x₁ a c false = res_rec at hha
                  cases res_rec with
                  | error => simp at hha
                  | ok val =>
                    simp only [Except.ok.injEq] at hha
                    unfold hasAttrInRecord at hattr_rec
                    split at hattr_rec
                    case h_1 qty hqty =>
                      simp only [ok] at hattr_rec
                      split at hattr_rec
                      · simp only [Except.ok.injEq] at hattr_rec
                        rw [← hattr_rec] at hha
                        rw [← hha] at heq; simp [TypedExpr.typeOf] at heq
                      · simp only [Except.ok.injEq] at hattr_rec
                        rw [← hattr_rec] at hha
                        rw [← hha] at heq; simp [TypedExpr.typeOf] at heq
                    case h_2 hfind_none =>
                      simp only [ok, Except.ok.injEq] at hattr_rec
                      have hio_ety : InstanceOfType env v (.entity ety) := by rwa [hety] at hio
                      have ⟨uid, huid_ty, hv_uid⟩ := instance_of_entity_type_is_entity hio_ety
                      subst hv_uid
                      simp [attrsOf] at hattrs
                      rw [← hattrs] at hfind
                      unfold Entities.attrsOrEmpty at hfind
                      split at hfind
                      case h_1 d hfind_ent =>
                        have hio_attrs := well_typed_entity_attributes hwf hfind_ent (by rwa [huid_ty])
                        have h_absent := absent_attribute_is_absent hio_attrs hfind_none
                        simp [h_absent] at hfind
                      case h_2 =>
                        simp at hfind
                case h_2 =>
                  split at hha
                  · simp only [ok, Except.ok.injEq] at hha
                    have hio_ety : InstanceOfType env v (.entity ety) := by rwa [hety] at hio
                    have ⟨uid, huid_ty, hv_uid⟩ := instance_of_entity_type_is_entity hio_ety
                    subst hv_uid
                    simp [attrsOf] at hattrs
                    rw [← hattrs] at hfind
                    unfold Entities.attrsOrEmpty at hfind
                    split at hfind
                    case h_1 d hfind_ent =>
                      have ⟨_, _, hwf_ent, _⟩ := hwf
                      simp [InstanceOfSchemaEntry] at hwf_ent
                      have hwf_d := hwf_ent uid d hfind_ent
                      rename_i heq_attrs_none h_action
                      cases hwf_d with
                      | inl h_entity_schema =>
                        unfold InstanceOfEntitySchemaEntry at h_entity_schema
                        rw [huid_ty] at h_entity_schema
                        obtain ⟨entry, hfind_ets, _⟩ := h_entity_schema
                        simp [EntitySchema.attrs?] at *
                        simp_all
                      | inr h_action_schema =>
                        unfold InstanceOfActionSchemaEntry at h_action_schema
                        have h_empty := h_action_schema.1
                        rw [h_empty] at hfind
                        simp at hfind
                    case h_2 =>
                      simp at hfind
                  · simp [err] at hha
              case h_3 => simp [err] at hha
          case h_2 hfind =>
            simp only [Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at hloop
            subst hloop
            cases bty' with
            | anyBool => simp [InstanceOfBoolType]
            | ff => simp [InstanceOfBoolType]
            | tt =>
              exfalso
              have h_false : hasAttr v a entities = .ok false := by
                unfold hasAttr
                simp only [bind, Except.bind, hattrs, Map.contains]
                rw [hfind]; rfl
              unfold typeOfHasAttr at hha
              split at hha
              case h_1 rty hrty =>
                -- Record case (knownToExist = true)
                simp only [ok, bind, Except.bind] at hha
                generalize hattr_rec : hasAttrInRecord rty x₁ a c true = res_rec at hha
                cases res_rec with
                | error => simp at hha
                | ok val =>
                  simp only [Except.ok.injEq] at hha
                  unfold hasAttrInRecord at hattr_rec
                  split at hattr_rec
                  case h_1 qty hqty_find =>
                    split at hattr_rec
                    case isTrue h_cond =>
                      simp only [ok, Except.ok.injEq] at hattr_rec
                      have hio_rec : InstanceOfType env v (.record rty) := by
                        rwa [hrty] at hio
                      simp [Bool.or_eq_true, decide_eq_true_eq] at h_cond
                      cases h_cond with
                      | inl h_cap =>
                        have h_cap_inv := hcap.1 x₁ a h_cap
                        simp only [EvaluatesTo] at h_cap_inv
                        rcases h_cap_inv with h | h | h | h
                        all_goals simp [evaluate, heval, hasAttr, bind, Except.bind, hattrs,
                          Map.contains, hfind] at h
                      | inr h_req =>
                        cases qty with
                        | required aty =>
                          have ⟨m, hm⟩ := instance_of_record_type_is_record hio_rec
                          subst hm
                          simp [attrsOf] at hattrs
                          subst hattrs
                          have h_present := required_attribute_is_present hio_rec hqty_find
                          obtain ⟨_, h_some⟩ := h_present
                          simp [hfind] at h_some
                        | optional _ => simp [Qualified.isRequired] at h_req
                    case isFalse =>
                      simp only [ok, Except.ok.injEq] at hattr_rec
                      rw [← hattr_rec] at hha
                      have h_type : val_ha.fst.typeOf = .bool .anyBool := by
                        have := Prod.ext_iff.mp hha
                        rw [← this.1]; simp [TypedExpr.typeOf]
                      rw [h_type] at heq; simp at heq
                  case h_2 =>
                    simp only [ok, Except.ok.injEq] at hattr_rec
                    rw [← hattr_rec] at hha
                    have h_type : val_ha.fst.typeOf = .bool .ff := by
                      have := Prod.ext_iff.mp hha
                      rw [← this.1]; simp [TypedExpr.typeOf]
                    rw [h_type] at heq; simp at heq
              case h_2 ety hety =>
                split at hha
                case h_1 rty' hattrs_schema =>
                  simp only [ok, bind, Except.bind] at hha
                  generalize hattr_rec : hasAttrInRecord rty' x₁ a c false = res_rec at hha
                  cases res_rec with
                  | error => simp at hha
                  | ok val =>
                    simp only [Except.ok.injEq] at hha
                    unfold hasAttrInRecord at hattr_rec
                    split at hattr_rec
                    case h_1 qty hqty_find =>
                      split at hattr_rec
                      case isTrue h_cond =>
                        simp only [ok, Except.ok.injEq] at hattr_rec
                        -- h_cond for entity (knownToExist=false): (x₁,.attr a) ∈ c || (required && false)
                        -- Second disjunct is false, so (x₁, .attr a) ∈ c
                        simp at h_cond
                        have h_cap_inv := hcap.1 x₁ a h_cond
                        simp only [EvaluatesTo] at h_cap_inv
                        rcases h_cap_inv with h | h | h | h
                        all_goals simp [evaluate, heval, h_false] at h
                      case isFalse =>
                        simp only [ok, Except.ok.injEq] at hattr_rec
                        rw [← hattr_rec] at hha
                        have h_type : val_ha.fst.typeOf = .bool .anyBool := by
                          have := Prod.ext_iff.mp hha
                          rw [← this.1]; simp [TypedExpr.typeOf]
                        rw [h_type] at heq; simp at heq
                    case h_2 =>
                      simp only [ok, Except.ok.injEq] at hattr_rec
                      rw [← hattr_rec] at hha
                      have h_type : val_ha.fst.typeOf = .bool .ff := by
                        have := Prod.ext_iff.mp hha
                        rw [← this.1]; simp [TypedExpr.typeOf]
                      rw [h_type] at heq; simp at heq
                case h_2 =>
                  split at hha
                  · -- action type → .ff, contradicts .tt
                    simp only [ok, Except.ok.injEq] at hha
                    have : val_ha.fst.typeOf = .bool .ff := by
                      rw [← hha]; simp [TypedExpr.typeOf]
                    rw [this] at heq; simp at heq
                  · simp [err] at hha
              case h_3 => simp [err] at hha
        case h_2 =>
          -- val_ha.fst.typeOf is not .bool, so bty = .anyBool
          simp only [Except.ok.injEq, Prod.mk.injEq] at hext
          obtain ⟨hbty_eq, _⟩ := hext
          rw [← hbty_eq]
          simp [InstanceOfBoolType]
    | cons b more =>
      -- Recursive case: typeOfExtHasAttr ty₁ x₁ (a :: b :: more) unfolds to
      -- typeOfGetAttr, typeOfHasAttr, then recurse on (b :: more) with tyNext
      simp only [typeOfExtHasAttr, bind, Except.bind] at hext
      cases hga : typeOfGetAttr ty₁ x₁ a c env with
      | error => simp [hga] at hext
      | ok val_ga =>
        simp only [hga] at hext
        obtain ⟨tyNext, _⟩ := val_ga
        cases hha_step : typeOfHasAttr ty₁ x₁ a c env with
        | error => simp [hha_step] at hext
        | ok val_ha =>
          simp only [hha_step] at hext
          -- hext now relates to the recursive call
          -- hasAttrs.loop v (a :: b :: more): attrsOf v, find? a, then recurse
          simp only [hasAttrs.loop] at hloop
          split at hloop
          case h_2 => simp at hloop -- attrsOf fails → contradiction
          rename_i r hattrs
          split at hloop
          case h_2 =>
            -- find? a = none → loop returns false
            simp at hloop; subst hloop
            -- Need InstanceOfBoolType false bty
            -- First resolve the typeOfExtHasAttr call in hext
            cases h_rec : typeOfExtHasAttr tyNext (Expr.getAttr x₁ a) (b :: more) (c ∪ val_ha.2) env with
            | error => simp [h_rec] at hext
            | ok val_rec =>
              simp only [h_rec] at hext
              -- Now split on val_ha.fst.typeOf
              split at hext
              · exfalso
                rename_i hfind_none _ heq_tt
                exact typeOfHasAttr_tt_contradicts_find_none hha_step heq_tt hio hcap heval hattrs hfind_none
              · simp only [Except.ok.injEq, Prod.mk.injEq] at hext
                rw [← hext.1]; simp [InstanceOfBoolType]
          case h_1 next hfind =>
            simp only [List.isEmpty] at hloop
            cases h_rec : typeOfExtHasAttr tyNext (Expr.getAttr x₁ a) (b :: more) (c ∪ val_ha.2) env with
            | error => simp [h_rec] at hext
            | ok val_rec =>
              simp only [h_rec] at hext
              split at hext
              · simp only [Except.ok.injEq, Prod.mk.injEq] at hext
                rw [← hext.1]
                have hio_next : InstanceOfType env next tyNext.typeOf :=
                  instance_of_getAttr_type hwf hga hio hattrs hfind heval
                have heval_next : evaluate (Expr.getAttr x₁ a) request entities = .ok next := by
                  simp [evaluate, heval, getAttr_ok_of_attrsOf_find hattrs hfind]
                have hcap_ci : CapabilitiesInvariant (c ∪ val_ha.2) request entities := by
                  apply capability_union_invariant hcap
                  cases typeOfHasAttr_caps_subset hha_step with
                  | inl h => rw [h]; exact empty_capabilities_invariant request entities
                  | inr h =>
                    rw [h]; constructor <;> intro _ _ hh <;> simp [Capabilities.singleton] at hh
                    · obtain ⟨hh₁, hh₂⟩ := hh; subst hh₁ hh₂
                      simp only [EvaluatesTo]
                      refine Or.inr (Or.inr (Or.inr ?_))
                      simp only [evaluate, heval, hasAttr, bind, Except.bind,
                        hattrs, Map.contains]
                      rw [hfind]; rfl
                exact ih h_rec hio_next hcap_ci heval_next hloop
              · -- non-.tt → bty = .anyBool
                simp only [Except.ok.injEq, Prod.mk.injEq] at hext
                rw [← hext.1]; simp [InstanceOfBoolType]

theorem type_of_extHasAttr_is_sound {x₁ : Expr} {a : Attr} {attrs : List Attr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.extHasAttr x₁ a attrs) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.extHasAttr x₁ a attrs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.extHasAttr x₁ a attrs) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  -- Extract sub-expression typing
  have hte : ∃ ty₁ c₁', typeOf x₁ c₁ env = .ok (ty₁, c₁') := by
    have h₃' := h₃
    simp only [typeOf, bind, Except.bind] at h₃'
    split at h₃'
    · simp at h₃'
    · rename_i val _
      exact ⟨val.1, val.2, by simp_all⟩
  obtain ⟨ty₁, c₁', hte⟩ := hte
  have ⟨hgci₁, v₁, hev₁, hio₁⟩ := ih h₁ h₂ hte
  -- Extract typeOfExtHasAttr from h₃
  have h₃' := h₃
  simp only [typeOf, bind, Except.bind, hte] at h₃'
  -- h₃' : typeOfExtHasAttr ty₁ x₁ (a :: attrs) c₁ env >>= ... = .ok (ty, c₂)
  have hext₀ : ∃ res, typeOfExtHasAttr ty₁ x₁ (a :: attrs) c₁ env = .ok res := by
    revert h₃'
    generalize typeOfExtHasAttr ty₁ x₁ (a :: attrs) c₁ env = res_ext
    intro h₃'
    cases res_ext with
    | error => simp at h₃'
    | ok val => exact ⟨val, rfl⟩
  obtain ⟨ext_res, hext₀⟩ := hext₀
  simp only [hext₀, ok, Except.ok.injEq, Prod.mk.injEq] at h₃'
  obtain ⟨hty_eq, hc₂_eq⟩ := h₃'
  have htyof : ty.typeOf = .bool ext_res.fst := by
    rw [← hty_eq]; simp [TypedExpr.typeOf]
  -- Evaluation unfolds to: evaluate x₁ >>= hasAttrs · a attrs
  have heval_ext : evaluate (.extHasAttr x₁ a attrs) request entities =
      (evaluate x₁ request entities >>= fun v => hasAttrs v a attrs entities) := by
    simp [evaluate]
  apply And.intro
  case left =>
    -- GuardedCapabilitiesInvariant
    intro heval_true
    subst hty_eq; subst hc₂_eq
    -- evaluate (.extHasAttr x₁ a attrs) = .ok true
    have ⟨v₁', hev_x₁, hhasattrs⟩ : ∃ v₁',
        evaluate x₁ request entities = .ok v₁' ∧
        hasAttrs v₁' a attrs entities = .ok true := by
      rw [heval_ext] at heval_true
      cases hev : evaluate x₁ request entities with
      | error => simp [hev] at heval_true
      | ok v₁' =>
        simp only [hev, Except.bind_ok] at heval_true
        exact ⟨v₁', rfl, heval_true⟩
    have hloop_ev : hasAttrs.loop v₁' (a :: attrs) entities = .ok true := hhasattrs
    -- Need InstanceOfType env v₁' ty₁.typeOf
    have hio₁' : InstanceOfType env v₁' ty₁.typeOf := by
      have ⟨_, _, _, hio_v⟩ := ih h₁ h₂ hte
      rename_i h₉
      simp only [EvaluatesTo] at h₉
      have ⟨_, v_ih, hev_ih, hio_ih⟩ := ih h₁ h₂ hte
      simp only [EvaluatesTo] at hev_ih
      rcases hev_ih with hev_ih | hev_ih | hev_ih | hev_ih
      · simp [hev_ih] at hev_x₁
      · simp [hev_ih] at hev_x₁
      · simp [hev_ih] at hev_x₁
      · rw [hev_ih] at hev_x₁
        simp at hev_x₁
        rw [← hev_x₁]
        exact hio_ih
    exact typeOfExtHasAttr_gci h₂ hext₀ hloop_ev hio₁' h₁ hev_x₁
  case right =>
    simp only [EvaluatesTo] at hev₁
    rcases hev₁ with hev₁ | hev₁ | hev₁ | hev₁
    · -- evaluate x₁ = .error .entityDoesNotExist
      have hinh := type_of_is_inhabited h₂.wf_env h₃
      obtain ⟨w, hw⟩ := hinh
      exact ⟨w, by simp [EvaluatesTo, heval_ext, hev₁], hw⟩
    · -- evaluate x₁ = .error .extensionError
      have hinh := type_of_is_inhabited h₂.wf_env h₃
      obtain ⟨w, hw⟩ := hinh
      exact ⟨w, by simp [EvaluatesTo, heval_ext, hev₁], hw⟩
    · -- evaluate x₁ = .error .arithBoundsError
      have hinh := type_of_is_inhabited h₂.wf_env h₃
      obtain ⟨w, hw⟩ := hinh
      exact ⟨w, by simp [EvaluatesTo, heval_ext, hev₁], hw⟩
    · -- evaluate x₁ = .ok v₁
      cases hha : hasAttrs v₁ a attrs entities with
      | ok r =>
        have ⟨b, hb⟩ := hasAttrs_ok_is_bool hha
        subst hb
        refine ⟨.prim (.bool b), ?_, ?_⟩
        · simp only [EvaluatesTo]
          rw [heval_ext, hev₁]; simp [hha]
        · rw [htyof]
          apply InstanceOfType.instance_of_bool
          exact typeOfExtHasAttr_bool_type_sound h₂ hext₀ hio₁ h₁ hev₁ (by simp [hasAttrs] at hha ⊢; exact hha)
      | error e =>
        have he := hasAttrs_safe_errors hha
        subst he
        -- Impossible: typeOfExtHasAttr succeeding + InstanceOfType means no typeError
        exfalso
        have hne := typeOfExtHasAttr_no_typeError h₂ hext₀ hio₁ h₁ hev₁
        exact hne .typeError (by simp [hasAttrs] at hha; exact hha)

end Cedar.Thm
