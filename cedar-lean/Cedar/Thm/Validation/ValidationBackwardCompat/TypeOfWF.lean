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

import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.ValidationPolicySlice.CheckEntities
import Cedar.Thm.Validation.ValidationBackwardCompat.LubWF
import Cedar.Thm.Data

/-!
# typeOf produces well-formed types

The core type soundness invariant: `typeOf` always produces `CedarType.WellFormed`
results, given a well-formed entity schema and valid entity checks.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

set_option maxHeartbeats 12800000

private theorem actionType_implies_IsActionEntityType {acts : ActionSchema} {ety : EntityType}
    (h : acts.actionType? ety = true) :
    acts.IsActionEntityType ety := by
  simp [ActionSchema.actionType?, Set.any, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨uid, hmem, heq⟩ := h
  exact ⟨uid, Map.in_keys_iff_contains.mp hmem, heq⟩

private theorem isValidEntityUID_implies_contains_ty {ets : EntitySchema} {uid : EntityUID}
    (h : ets.isValidEntityUID uid = true) :
    ets.contains uid.ty := by
  simp only [EntitySchema.isValidEntityUID] at h
  cases hf : ets.find? uid.ty with
  | none => simp [hf] at h
  | some _ => simp [EntitySchema.contains, hf]

theorem typeOf_produces_wf_type (expr : Expr) (c : Capabilities)
    {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities}
    (hets_wf : EntitySchema.WellFormed env env.ets)
    (hce : checkEntities ⟨env.ets, env.acts⟩ expr = .ok ())
    (hok : typeOf expr c env = .ok (tx, c'))
    (hdisjoint : ∀ uid, env.acts.contains uid = true → ¬ env.ets.contains uid.ty)
    (hreqty_action : env.acts.contains env.reqty.action = true)
    (hreqty_principal : env.ets.contains env.reqty.principal ∨ env.acts.actionType? env.reqty.principal)
    (hreqty_resource : env.ets.contains env.reqty.resource ∨ env.acts.actionType? env.reqty.resource)
    (hctx_wf : (CedarType.record env.reqty.context).WellFormed env) :
    CedarType.WellFormed env tx.typeOf := by
  match expr with
  | .lit (.bool true) =>
    simp [typeOf, typeOfLit, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]; exact .bool_wf
  | .lit (.bool false) =>
    simp [typeOf, typeOfLit, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]; exact .bool_wf
  | .lit (.int _) =>
    simp [typeOf, typeOfLit, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]; exact .int_wf
  | .lit (.string _) =>
    simp [typeOf, typeOfLit, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]; exact .string_wf
  | .lit (.entityUID uid) =>
    simp only [checkEntities] at hce
    split at hce
    · rename_i hvalid
      simp [typeOf, typeOfLit, hvalid, ok, Function.comp] at hok
      obtain ⟨h₁, _⟩ := hok; subst h₁
      simp [TypedExpr.typeOf]
      apply CedarType.WellFormed.entity_wf
      simp [EntityType.WellFormed]
      cases hv : env.ets.isValidEntityUID uid
      · simp [hv] at hvalid
        right
        exact ⟨uid, hvalid, rfl⟩
      · left
        exact isValidEntityUID_implies_contains_ty hv
    · contradiction
  | .var .principal =>
    simp [typeOf, typeOfVar, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]
    apply CedarType.WellFormed.entity_wf
    simp [EntityType.WellFormed]
    cases hreqty_principal with
    | inl h => left; exact h
    | inr h => right; exact actionType_implies_IsActionEntityType h
  | .var .action =>
    simp [typeOf, typeOfVar, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]
    apply CedarType.WellFormed.entity_wf
    simp [EntityType.WellFormed]
    right; exact ⟨env.reqty.action, hreqty_action, rfl⟩
  | .var .resource =>
    simp [typeOf, typeOfVar, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]
    apply CedarType.WellFormed.entity_wf
    simp [EntityType.WellFormed]
    cases hreqty_resource with
    | inl h => left; exact h
    | inr h => right; exact actionType_implies_IsActionEntityType h
  | .var .context =>
    simp [typeOf, typeOfVar, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]
    exact hctx_wf
  | .ite x₁ x₂ x₃ =>
    unfold checkEntities at hce
    have hce₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ = .ok () := by
      cases h₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ <;> simp_all
    have hce₂ : checkEntities ⟨env.ets, env.acts⟩ x₂ = .ok () := by
      cases h₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ <;> simp_all
      cases h₂ : checkEntities ⟨env.ets, env.acts⟩ x₂ <;> simp_all
    have hce₃ : checkEntities ⟨env.ets, env.acts⟩ x₃ = .ok () := by
      simp [hce₁, hce₂] at hce; exact hce
    simp only [typeOf] at hok
    cases h₁ : typeOf x₁ c env with
    | error => simp [h₁] at hok
    | ok val₁ =>
      obtain ⟨tx₁, c₁⟩ := val₁
      simp [h₁] at hok
      simp only [typeOfIf] at hok
      split at hok
      · -- .bool .tt: result is from x₂
        cases h₂ : typeOf x₂ (c ∪ c₁) env with
        | error => simp [h₂] at hok
        | ok val₂ =>
          obtain ⟨tx₂, c₂⟩ := val₂
          simp [h₂, ok] at hok
          obtain ⟨h, _⟩ := hok; subst h
          simp [TypedExpr.typeOf]
          exact typeOf_produces_wf_type x₂ (c ∪ c₁) hets_wf hce₂ h₂ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
      · -- .bool .ff: result is from x₃
        cases h₃ : typeOf x₃ c env with
        | error => simp [h₃] at hok
        | ok val₃ =>
          obtain ⟨tx₃, c₃⟩ := val₃
          simp [h₃, ok] at hok
          obtain ⟨h, _⟩ := hok; subst h
          simp [TypedExpr.typeOf]
          exact typeOf_produces_wf_type x₃ c hets_wf hce₃ h₃ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
      · -- .bool .anyBool: result is lub? of x₂.typeOf and x₃.typeOf
        cases h₂ : typeOf x₂ (c ∪ c₁) env with
        | error => simp [h₂] at hok
        | ok val₂ =>
          obtain ⟨tx₂, c₂⟩ := val₂
          simp [h₂] at hok
          cases h₃ : typeOf x₃ c env with
          | error => simp [h₃] at hok
          | ok val₃ =>
            obtain ⟨tx₃, c₃⟩ := val₃
            simp [h₃] at hok
            split at hok
            · rename_i ty hlub
              simp [ok] at hok
              obtain ⟨h, _⟩ := hok; subst h
              simp [TypedExpr.typeOf]
              have hwf₂ := typeOf_produces_wf_type x₂ (c ∪ c₁) hets_wf hce₂ h₂ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
              exact lub_preserves_wf_left hwf₂ hlub
            · simp [err] at hok
      · simp [err] at hok
  | .and x₁ x₂ =>
    have hce₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce
      cases h : checkEntities ⟨env.ets, env.acts⟩ x₁ with
      | error => simp [h] at hce
      | ok u => cases u; rfl
    have hce₂ : checkEntities ⟨env.ets, env.acts⟩ x₂ = .ok () := by
      unfold checkEntities at hce; simp [hce₁] at hce; exact hce
    simp only [typeOf] at hok
    cases h₁ : typeOf x₁ c env with
    | error => simp [h₁] at hok
    | ok val₁ =>
      obtain ⟨tx₁, c₁⟩ := val₁
      simp [h₁] at hok
      simp only [typeOfAnd] at hok
      split at hok
      · -- .bool .ff: result is tx₁ itself which has type .bool .ff
        simp [ok] at hok
        obtain ⟨h, _⟩ := hok; subst h
        simp [TypedExpr.typeOf]
        have := typeOf_produces_wf_type x₁ c hets_wf hce₁ h₁ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
        exact this
      · -- .bool ty₁: typeOfAnd continued
        cases h₂ : typeOf x₂ (c ∪ c₁) env with
        | error => simp [h₂] at hok
        | ok val₂ =>
          obtain ⟨tx₂, c₂⟩ := val₂
          simp [h₂] at hok
          -- hok now contains the result of matching on tx₂.typeOf
          -- All successful arms produce (.bool _) as result type
          split at hok
          all_goals (simp [ok, err] at hok)
          all_goals (obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf)
      · -- unexpectedType case
        simp [err] at hok
  | .or x₁ x₂ =>
    have hce₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce
      cases h : checkEntities ⟨env.ets, env.acts⟩ x₁ with
      | error => simp [h] at hce
      | ok u => cases u; rfl
    have hce₂ : checkEntities ⟨env.ets, env.acts⟩ x₂ = .ok () := by
      unfold checkEntities at hce; simp [hce₁] at hce; exact hce
    simp only [typeOf] at hok
    cases h₁ : typeOf x₁ c env with
    | error => simp [h₁] at hok
    | ok val₁ =>
      obtain ⟨tx₁, c₁⟩ := val₁
      simp [h₁] at hok
      simp only [typeOfOr] at hok
      split at hok
      · -- .bool .tt: result is tx₁ itself
        simp [ok] at hok
        obtain ⟨h, _⟩ := hok; subst h
        simp [TypedExpr.typeOf]
        exact typeOf_produces_wf_type x₁ c hets_wf hce₁ h₁ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
      · -- .bool .ff
        cases h₂ : typeOf x₂ c env with
        | error => simp [h₂] at hok
        | ok val₂ =>
          obtain ⟨tx₂, c₂⟩ := val₂
          simp [h₂] at hok
          split at hok
          all_goals (simp [ok, err] at hok)
          all_goals (obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf])
          all_goals exact typeOf_produces_wf_type x₂ c hets_wf hce₂ h₂ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
      · -- .bool _
        cases h₂ : typeOf x₂ c env with
        | error => simp [h₂] at hok
        | ok val₂ =>
          obtain ⟨tx₂, c₂⟩ := val₂
          simp [h₂] at hok
          split at hok
          all_goals (simp [ok, err] at hok)
          all_goals (obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf)
      · simp [err] at hok
  | .unaryApp op x₁ =>
    have hce₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ = .ok () := by
      cases op with
      | not | neg | like | isEmpty =>
        simp only [checkEntities] at hce; exact hce
      | is ety =>
        simp only [checkEntities] at hce
        split at hce
        · exact hce
        · contradiction
    simp only [typeOf] at hok
    cases h₁ : typeOf x₁ c env with
    | error => simp [h₁] at hok
    | ok val₁ =>
      obtain ⟨tx₁, c₁⟩ := val₁
      simp [h₁] at hok
      simp only [typeOfUnaryApp] at hok
      split at hok
      · -- .not, .bool x
        simp [ok, Function.comp] at hok
        obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
      · -- .neg, .int
        simp [ok, Function.comp] at hok
        obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .int_wf
      · -- .isEmpty, .set _
        simp [ok, Function.comp] at hok
        obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
      · -- .like _, .string
        simp [ok, Function.comp] at hok
        obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
      · -- .is ety₁, .entity ety₂
        simp [ok, Function.comp] at hok
        obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
      · -- catch-all error
        simp [err] at hok
  | .binaryApp op x₁ x₂ =>
    have hce₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce
      cases h : checkEntities ⟨env.ets, env.acts⟩ x₁ with
      | error => simp [h] at hce
      | ok => cases ‹Unit›; rfl
    have hce₂ : checkEntities ⟨env.ets, env.acts⟩ x₂ = .ok () := by
      unfold checkEntities at hce; simp [hce₁] at hce; exact hce
    simp only [typeOf] at hok
    cases h₁ : typeOf x₁ c env with
    | error => simp [h₁] at hok
    | ok val₁ =>
      obtain ⟨tx₁, c₁⟩ := val₁
      simp [h₁] at hok
      cases h₂ : typeOf x₂ c env with
      | error => simp [h₂] at hok
      | ok val₂ =>
        obtain ⟨tx₂, c₂⟩ := val₂
        simp [h₂] at hok
        simp only [typeOfBinaryApp] at hok
        -- Most arms produce .bool _ or .int → trivially WF
        -- .getTag may produce a type from the schema
        split at hok
        · -- .eq: typeOfEq produces .bool _
          simp only [typeOfEq] at hok
          split at hok
          · split at hok <;> simp [ok] at hok <;> (obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf)
          · split at hok
            · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
            · split at hok
              · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
              · simp [err] at hok
        · -- .mem entity entity: produces .bool _
          simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · -- .mem entity (set entity): produces .bool _
          simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · -- .hasTag entity string: produces .bool _ via typeOfHasTag
          simp only [typeOfHasTag] at hok
          split at hok
          · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
          · split at hok <;> simp [ok] at hok <;> (obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf)
          · split at hok
            · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
            · simp [err] at hok
        · -- .getTag entity string: produces ty from tags?
          rename_i ety₁ _ _
          simp only [typeOfGetTag] at hok
          split at hok
          · simp [err] at hok
          · rename_i htags
            split at hok
            · simp [ok] at hok
              obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]
              -- ty comes from ets.tags? ety₁ = some (some ty)
              -- Use schema WF to show ty is WF
              simp only [EntitySchema.tags?, Option.map_eq_some_iff] at htags
              obtain ⟨entry, hfind_e, htags_eq⟩ := htags
              have hentry_wf := hets_wf.2 ety₁ entry hfind_e
              cases entry with
              | standard s =>
                simp [EntitySchemaEntry.WellFormed, StandardSchemaEntry.WellFormed] at hentry_wf
                have ⟨_, _, _, _, htag_wf⟩ := hentry_wf
                simp [EntitySchemaEntry.tags?] at htags_eq
                exact (htag_wf _ htags_eq).1
              | enum _ =>
                simp [EntitySchemaEntry.tags?] at htags_eq
            · simp [err] at hok
          · simp [err] at hok
        · -- .less int int: produces .bool _
          simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · -- .add: produces .int
          simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .int_wf
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .int_wf
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .int_wf
        · -- .contains: ifLubThenBool → .bool _
          simp only [ifLubThenBool] at hok
          split at hok <;> simp [ok, err] at hok
          obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp only [ifLubThenBool] at hok
          split at hok <;> simp [ok, err] at hok
          obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp only [ifLubThenBool] at hok
          split at hok <;> simp [ok, err] at hok
          obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp [err] at hok
  | .hasAttr x₁ _ =>
    have hce₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce; exact hce
    simp only [typeOf] at hok
    cases h₁ : typeOf x₁ c env with
    | error => simp [h₁] at hok
    | ok val₁ =>
      obtain ⟨tx₁, c₁⟩ := val₁
      simp [h₁] at hok
      simp only [typeOfHasAttr] at hok
      split at hok
      · -- .record: hasAttrInRecord → .bool _
        simp only [hasAttrInRecord] at hok
        split at hok
        · split at hok <;> simp [ok] at hok <;> (obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf)
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
      · -- .entity: hasAttrInRecord or .bool .ff or error
        split at hok
        · simp only [hasAttrInRecord] at hok
          split at hok
          · split at hok <;> simp [ok] at hok <;> (obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf)
          · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · split at hok
          · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
          · simp [err] at hok
      · simp [err] at hok
  | .getAttr x₁ a =>
    have hce₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce; exact hce
    simp only [typeOf] at hok
    cases h₁ : typeOf x₁ c env with
    | error => simp [h₁] at hok
    | ok val₁ =>
      obtain ⟨tx₁, c₁⟩ := val₁
      simp [h₁] at hok
      simp only [typeOfGetAttr] at hok
      split at hok
      · -- .record rty: getAttrInRecord → aty where rty.find? a = some qty
        rename_i rty _
        simp only [getAttrInRecord] at hok
        split at hok
        · -- .some (.required aty)
          rename_i aty hfind
          simp [ok] at hok
          obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]
          -- tx₁.typeOf = .record rty, and by IH it's WF
          have hwf₁ := typeOf_produces_wf_type x₁ c hets_wf hce₁ h₁ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
          -- hwf₁ : CedarType.WellFormed env (.record rty)
          -- But wait - tx₁.typeOf might not be exactly .record rty if tx₁ is more complex
          -- Actually, the split on tx₁.typeOf = .record rty already establishes this
          have hwf_record : (CedarType.record rty).WellFormed env := by
            have : tx₁.typeOf = .record rty := by assumption
            rw [← this]; exact hwf₁
          cases hwf_record with
          | record_wf _ hattr =>
            have hqty_wf := hattr a (.required aty) hfind
            cases hqty_wf with
            | required_wf h => exact h
        · -- .some (.optional aty)
          rename_i aty hfind
          split at hok
          · simp [ok] at hok
            obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]
            have hwf₁ := typeOf_produces_wf_type x₁ c hets_wf hce₁ h₁ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
            have hwf_record : (CedarType.record rty).WellFormed env := by
              have : tx₁.typeOf = .record rty := by assumption
              rw [← this]; exact hwf₁
            cases hwf_record with
            | record_wf _ hattr =>
              have hqty_wf := hattr a (.optional aty) hfind
              cases hqty_wf with
              | optional_wf h => exact h
          · simp [err] at hok
        · simp [err] at hok
      · -- .entity ety: getAttrInRecord on ets.attrs? ety
        rename_i ety _
        split at hok
        · rename_i rty hattrs
          simp only [getAttrInRecord] at hok
          split at hok
          · rename_i aty hfind
            simp [ok] at hok
            obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]
            -- ety is in ets (from attrs? succeeding), attrs? gives WF record from schema WF
            have hwf_record : (CedarType.record rty).WellFormed env := by
              simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hattrs
              obtain ⟨entry, hfind_e, hattrs_eq⟩ := hattrs
              have hentry_wf := hets_wf.2 ety entry hfind_e
              cases entry with
              | standard s =>
                simp [EntitySchemaEntry.WellFormed, StandardSchemaEntry.WellFormed] at hentry_wf
                have ⟨_, _, hwf, _⟩ := hentry_wf
                simpa [EntitySchemaEntry.attrs, ← hattrs_eq] using hwf
              | enum _ =>
                simp [EntitySchemaEntry.attrs] at hattrs_eq
                subst hattrs_eq
                exact .record_wf (by constructor) (by intro _ _ h; simp [Map.find?] at h)
            cases hwf_record with
            | record_wf _ hattr =>
              have hqty_wf := hattr a (.required aty) hfind
              cases hqty_wf with
              | required_wf h => exact h
          · rename_i aty hfind
            split at hok
            · simp [ok] at hok
              obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]
              have hwf_record : (CedarType.record rty).WellFormed env := by
                simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hattrs
                obtain ⟨entry, hfind_e, hattrs_eq⟩ := hattrs
                have hentry_wf := hets_wf.2 ety entry hfind_e
                cases entry with
                | standard s =>
                  simp [EntitySchemaEntry.WellFormed, StandardSchemaEntry.WellFormed] at hentry_wf
                  have ⟨_, _, hwf, _⟩ := hentry_wf
                  simpa [EntitySchemaEntry.attrs, ← hattrs_eq] using hwf
                | enum _ =>
                  simp [EntitySchemaEntry.attrs] at hattrs_eq
                  subst hattrs_eq
                  exact .record_wf (by constructor) (by intro _ _ h; simp [Map.find?] at h)
              cases hwf_record with
              | record_wf _ hattr =>
                have hqty_wf := hattr a (.optional aty) hfind
                cases hqty_wf with
                | optional_wf h => exact h
            · simp [err] at hok
          · simp [err] at hok
        · simp [err] at hok
      · simp [err] at hok
  | .set (x₀ :: xtl) =>
    have hce_all : ∀ x ∈ (x₀ :: xtl), checkEntities ⟨env.ets, env.acts⟩ x = .ok () := by
      intro x hx
      have hce' : (x₀ :: xtl).attach.forM (fun ⟨x, _⟩ => checkEntities ⟨env.ets, env.acts⟩ x) = .ok () := by
        simp only [checkEntities] at hce; exact hce
      have := List.forM_ok_implies_all_ok' hce' ⟨x, hx⟩ (List.mem_attach _ ⟨x, hx⟩)
      simpa using this
    have ⟨_, txs, ty, htx_eq, helem⟩ := type_of_set_inversion hok
    rw [htx_eq]; simp [TypedExpr.typeOf]
    have hx₀_mem : x₀ ∈ (x₀ :: xtl) := List.Mem.head _
    obtain ⟨tx₀, c₀, _, htypeOf₀, hlub₀⟩ := helem x₀ hx₀_mem
    have hwf₀ := typeOf_produces_wf_type x₀ c hets_wf (hce_all x₀ hx₀_mem) htypeOf₀
      hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
    exact .set_wf (lub_preserves_wf_left hwf₀ hlub₀)
  | .set [] =>
    simp [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env)),
      typeOfSet, ok, err] at hok
  | .record axs =>
    have hce_all : ∀ ax ∈ axs, checkEntities ⟨env.ets, env.acts⟩ ax.snd = .ok () := by
      intro ax hax
      have hce' := hce; simp only [checkEntities] at hce'
      have hmem : ⟨ax, List.sizeOf_snd_lt_sizeOf_list hax⟩ ∈ axs.attach₂ := by
        simp only [List.attach₂, List.mem_pmap]
        exact ⟨ax, hax, rfl⟩
      exact List.forM_ok_implies_all_ok' hce' _ hmem
    simp only [typeOf,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env).map (fun (ty, _) => (ax.fst, ty))) axs] at hok
    -- Extract mapM result
    have hbind := hok
    simp only [bind, Except.bind] at hbind
    split at hbind
    · exact absurd hbind (by simp)
    · rename_i atys hmapM_eq
      simp [ok] at hbind
      obtain ⟨h, _⟩ := hbind; subst h; simp [TypedExpr.typeOf]
      apply CedarType.WellFormed.record_wf
      · exact Map.make_wf _
      · intro attr qty hfind
        -- From (Map.make mapped_list).find? attr = some qty, derive qty is in mapped_list
        have hfind_list : (List.find? (fun x => x.fst == attr) (atys.map (fun (a, ty) => (a, Qualified.required ty.typeOf)))).map Prod.snd = some qty := by
          rw [← Map.make_find?_eq_list_find?]; exact hfind
        -- Extract the found element
        cases hfl : List.find? (fun x => x.fst == attr) (atys.map (fun (a, ty) => (a, Qualified.required ty.typeOf))) with
        | none => simp [hfl] at hfind_list
        | some p =>
          simp [hfl] at hfind_list
          subst hfind_list
          -- p ∈ mapped_list and p.fst == attr
          have hp_mem := List.mem_of_find?_eq_some hfl
          rw [List.mem_map] at hp_mem
          obtain ⟨⟨a_i, ty_i⟩, hmem_atys, heq_p⟩ := hp_mem
          -- p = (a_i, .required ty_i.typeOf)
          -- Goal is QualifiedType.WellFormed env p.snd
          have h_snd : p.snd = Qualified.required ty_i.typeOf := by
            have := congrArg Prod.snd heq_p; exact this.symm
          rw [h_snd]
          -- ty_i ∈ atys came from mapM
          have ⟨ax_i, hax_mem, hmap_ok⟩ := List.mapM_ok_implies_all_from_ok hmapM_eq (a_i, ty_i) hmem_atys
          -- hmap_ok : (typeOf ax_i.snd c env).map (fun (ty, _) => (ax_i.fst, ty)) = .ok (a_i, ty_i)
          -- Extract the typeOf result from the Except.map
          cases htypeOf_ok : typeOf ax_i.snd c env with
          | error => simp [Except.map, htypeOf_ok] at hmap_ok
          | ok val =>
            obtain ⟨tx_i, c_i⟩ := val
            simp [Except.map, htypeOf_ok] at hmap_ok
            obtain ⟨_, h_ty⟩ := hmap_ok
            subst h_ty
            have _hlt : sizeOf ax_i.snd < 1 + sizeOf axs :=
              List.sizeOf_snd_lt_sizeOf_list hax_mem
            have hwf_i := typeOf_produces_wf_type ax_i.snd c hets_wf
              (hce_all ax_i hax_mem) htypeOf_ok
              hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
            exact .required_wf hwf_i
  | .call xfn xs =>
    simp only [typeOf] at hok
    -- Extract the mapM₁ result
    have hbind := hok
    simp only [bind, Except.bind] at hbind
    split at hbind
    · exact absurd hbind (by simp)
    · rename_i tys _
      -- Now tys is the result of mapM₁ and hbind : typeOfCall xfn tys xs = .ok (tx, c')
      simp only [typeOfCall] at hbind
      -- All arms produce .ext _, .bool _, or .int
      split at hbind
      all_goals (try (simp only [typeOfConstructor] at hbind))
      all_goals (try (split at hbind))
      all_goals (try (split at hbind))
      all_goals (simp [ok, err] at hbind)
      all_goals (try (obtain ⟨h, _⟩ := hbind; subst h; simp [TypedExpr.typeOf]))
      all_goals (first | exact .ext_wf | exact .bool_wf | exact .int_wf)
  termination_by sizeOf expr

end Cedar.Thm
