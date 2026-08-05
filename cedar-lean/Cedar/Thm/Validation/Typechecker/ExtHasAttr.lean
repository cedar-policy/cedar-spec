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
  {res : TypedExpr × Capabilities}
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
      -- attrsOf v succeeded
      split at he
      case h_1 next hfind =>
        -- m.find? a = .some next
        split at he
        case isTrue => simp at he -- rest.isEmpty: .ok true ≠ .error
        case isFalse hne =>
          -- rest is non-empty, so he : hasAttrs.loop next rest = .error e
          -- Need to show next is well-typed for the recursive call
          -- Unfold typeOfExtHasAttr
          cases rest with
          | nil => simp at hne
          | cons b rest' =>
            -- typeOfExtHasAttr ty₁ x₁ (a :: b :: rest') c env = .ok res
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
  {res : TypedExpr × Capabilities}
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
      | ok _ =>
        simp only [h₅, Except.ok.injEq] at hext
        -- hext : (ty₁, val_ha.2) = res
        rw [← hext]
        -- val_ha.2 is ∅ or singleton x₁ (.attr a)
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
          obtain ⟨_, ci⟩ := val_ha
          cases h₇ : typeOfExtHasAttr tyNext (Expr.getAttr x₁ a) (b :: rest') (c ∪ ci) env with
          | error => simp [h₇] at hext
          | ok val_rec =>
            simp only [h₇, Except.ok.injEq] at hext
            -- res.2 = ci ∪ val_rec.2
            obtain ⟨_, _⟩ := hext
            simp_all only [ExceptT.stM_eq, Prod.forall, reduceCtorEq, false_or]
            -- ci is valid (same as before)
            have h₉ : CapabilitiesInvariant ci request entities := by
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
            -- CapabilitiesInvariant (c ∪ ci)
            have hc_ci_inv : CapabilitiesInvariant (c ∪ ci) request entities :=
              capability_union_invariant hcap h₉
            have hrec_inv : CapabilitiesInvariant val_rec.2 request entities := by
              apply ih
              · exact h₇
              · exact h₃
              · exact hio_next
              · exact hc_ci_inv
              · exact heval_next
            exact capability_union_invariant h₉ hrec_inv

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
  have htyof : ty.typeOf = .bool .anyBool := by
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
          exact InstanceOfType.instance_of_bool b .anyBool (by simp [InstanceOfBoolType])
      | error e =>
        have he := hasAttrs_safe_errors hha
        subst he
        -- Impossible: typeOfExtHasAttr succeeding + InstanceOfType means no typeError
        exfalso
        have hne := typeOfExtHasAttr_no_typeError h₂ hext₀ hio₁ h₁ hev₁
        exact hne .typeError (by simp [hasAttrs] at hha; exact hha)

end Cedar.Thm
