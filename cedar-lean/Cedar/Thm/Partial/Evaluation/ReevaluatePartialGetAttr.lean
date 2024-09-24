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

import Cedar.Partial.Evaluator
import Cedar.Thm.Data.Map
import Cedar.Thm.Partial.Evaluation.EvaluatePartialGetAttr
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.ReevaluateGetAttr

open Cedar.Data
open Cedar.Partial (Subsmap)
open Cedar.Spec (Attr EntityUID Error Expr Prim Result)

/--
  `Partial.getAttr` on a `Spec.Value.record` returns the same result regardless
  of the `entities` parameter
-/
theorem partialGetAttr_record_entities (m : Map Attr Spec.Value) (attr : Attr) (entities₁ entities₂ : Partial.Entities) :
  Partial.getAttr (.record m) attr entities₁ = Partial.getAttr (.record m) attr entities₂
:= by
  simp [Partial.getAttr, Partial.attrsOf]

/--
  `Partial.attrsOf` on a `Spec.Value.record` never returns a map containing any
  residuals
-/
theorem partialAttrsOf_record {m : Map Attr Spec.Value} {entities : Partial.Entities} :
  Partial.attrsOf (.record m) entities.attrs = .ok attrs →
  ∀ val ∈ attrs.values, match val with | .value _ => true | .residual _ => false
:= by
  simp [Partial.attrsOf]
  intro h pval h₁ ; subst h
  simp [Map.values_mapOnValues] at h₁
  replace ⟨val, _, h₁⟩ := h₁ ; subst h₁
  simp

/--
  `Partial.getAttr` on a `Spec.Value.record` never returns a residual
-/
theorem partialGetAttr_record (m : Map Attr Spec.Value) (attr : Attr) (entities : Partial.Entities) :
  match Partial.getAttr (.record m) attr entities with
  | .ok (.value _) => true
  | .ok (.residual _) => false
  | .error _ => true
:= by
  simp [Partial.getAttr]
  cases h₁ : Partial.attrsOf (.record m) entities.attrs <;> simp
  case ok attrs =>
    have h₂ := partialAttrsOf_record h₁
    rcases Map.findOrErr_returns attrs attr Error.attrDoesNotExist with h₃ | h₃
    · replace ⟨pval, h₃⟩ := h₃
      cases pval
      case value => simp [h₃]
      case residual r =>
        specialize h₂ (.residual r) (Map.findOrErr_ok_implies_in_values h₃)
        simp at h₂
    · simp [h₃]

/--
  If `Partial.getAttr` on an `entityUID` returns a residual, re-evaluating that
  residual with a substitution on `entities` is equivalent to substituting
  first, calling `Partial.getAttr` on the substituted entities, and evaluating
  the result
-/
theorem reeval_eqv_substituting_first_partialGetAttr_entityUID (uid : EntityUID) (attr : Attr) {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  (Partial.getAttr (.prim (.entityUID uid)) attr entities >>= λ residual => Partial.evaluateValue (residual.subst subsmap) (entities.subst subsmap)) =
  (Partial.getAttr (.prim (.entityUID uid)) attr (entities.subst subsmap) >>= λ v => Partial.evaluateValue v (entities.subst subsmap))
:= by
  unfold Partial.getAttr
  cases h₁ : Partial.attrsOf (.prim (.entityUID uid)) entities.attrs
  case error e => simp [EvaluateGetAttr.attrsOf_subst_preserves_errors h₁]
  case ok attrs =>
    have wf_attrs := EvaluateGetAttr.attrsOf_wf (by simp [Spec.Value.WellFormed, Prim.WellFormed]) wf_e h₁
    simp only [Partial.attrsOf, Except.bind_ok, bind_assoc] at *
    rcases Map.findOrErr_returns attrs attr Error.attrDoesNotExist with h₂ | h₂
    · replace ⟨pval, h₂⟩ := h₂
      simp only [h₂, Except.bind_ok]
      replace h₂ := Map.findOrErr_ok_implies_in_kvs h₂
      have wf₁ : pval.WellFormed := by
        simp [Partial.Entities.attrs] at h₁
        cases h₃ : entities.es.findOrErr uid Error.entityDoesNotExist
        <;> simp [h₃] at h₁
        case ok edata =>
          subst h₁
          replace h₃ := Map.findOrErr_ok_implies_in_values h₃
          simp [Partial.Entities.WellFormed, Partial.EntityData.WellFormed] at wf_e
          exact (wf_e.right edata h₃).right.right pval (Map.in_list_in_values h₂)
      have ⟨attrs', h₂, h₃⟩ := Subst.entities_subst_preserves_attrs subsmap h₁ h₂
      have wf_attrs' := EvaluateGetAttr.partialEntities_attrs_wf (Subst.entities_subst_preserves_wf wf_e wf_s) h₂
      simp [h₂]
      cases pval
      case residual r => simp [(Map.findOrErr_ok_iff_in_kvs wf_attrs'.left).mpr h₃]
      case value v =>
        simp [Subst.subst_concrete_value, Partial.evaluateValue]
        simp [Subst.subst_concrete_value] at h₃
        apply Eq.symm
        rcases Map.findOrErr_returns attrs' attr Error.attrDoesNotExist with h₄ | h₄
        · replace ⟨pval, h₄⟩ := h₄
          have wf₂ : pval.WellFormed := wf_attrs'.right pval (Map.findOrErr_ok_implies_in_values h₄)
          simp [h₄]
          cases pval
          case residual r =>
            replace h₄ := Map.findOrErr_ok_implies_in_kvs h₄
            have h₅ := Map.key_maps_to_one_value attr _ _ attrs' wf_attrs'.left h₃ h₄
            simp at h₅
          case value v' =>
            simp only [Partial.Value.WellFormed] at wf₂
            simp only [Partial.evaluateValue, Except.ok.injEq, Partial.Value.value.injEq]
            replace h₄ := Map.findOrErr_ok_implies_in_kvs h₄
            suffices Partial.Value.value v = Partial.Value.value v' by simp at this ; exact this.symm
            exact Map.key_maps_to_one_value _ _ _ attrs' wf_attrs'.left h₃ h₄
        · rw [Map.findOrErr_err_iff_not_in_keys wf_attrs'.left] at h₄
          replace h₃ := Map.in_list_in_keys h₃
          contradiction
    · simp [h₂]
      cases h₃ : (entities.subst subsmap).attrs uid
      case error e' =>
        simp [(Subst.entities_subst_preserves_error_attrs subsmap).mpr h₃] at h₁
      case ok attrs' =>
        simp only [Except.bind_ok]
        have ⟨attrs'', h₃', h₄⟩ := Subst.entities_subst_preserves_absent_attrs subsmap h₁ (k := attr) ((Map.findOrErr_err_iff_not_in_keys wf_attrs.left).mp h₂)
        simp only [h₃, Except.ok.injEq] at h₃' ; subst attrs''
        have wf_attrs' := EvaluateGetAttr.partialEntities_attrs_wf (Subst.entities_subst_preserves_wf wf_e wf_s) h₃
        rw [← Map.findOrErr_err_iff_not_in_keys wf_attrs'.left (e := Error.attrDoesNotExist)] at h₄
        simp [h₄]

/--
  If `Partial.getAttr` returns a residual, re-evaluating that residual with a
  substitution on `entities` is equivalent to substituting first, calling
  `Partial.getAttr` on the substituted entities, and evaluating the result
-/
theorem reeval_eqv_substituting_first_partialGetAttr (v₁ : Spec.Value) (attr : Attr) {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_v : v₁.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  (Partial.getAttr v₁ attr entities >>= λ residual => Partial.evaluateValue (residual.subst subsmap) (entities.subst subsmap)) =
  (Partial.getAttr v₁ attr (entities.subst subsmap) >>= λ v => Partial.evaluateValue v (entities.subst subsmap))
:= by
  cases v₁
  case prim p =>
    cases p
    case entityUID uid => exact reeval_eqv_substituting_first_partialGetAttr_entityUID uid attr wf_e wf_s
    all_goals {
      unfold Partial.getAttr
      cases hv₁ : Partial.attrsOf _ entities.attrs
      case error e => simp [EvaluateGetAttr.attrsOf_subst_preserves_errors hv₁]
      case ok attrs => simp [Partial.attrsOf] at hv₁
    }
  case record m =>
    rw [partialGetAttr_record_entities m attr (entities.subst subsmap) entities]
    cases h₁ : Partial.getAttr (.record m) attr entities <;> simp
    case ok pval =>
      have wf₁ : pval.WellFormed := EvaluateGetAttr.getAttr_wf wf_v wf_e _ h₁
      cases pval
      case value v => simp [Subst.subst_concrete_value]
      case residual r =>
        have h₂ := partialGetAttr_record m attr entities
        simp [h₁] at h₂
  all_goals {
    unfold Partial.getAttr
    cases hv₁ : Partial.attrsOf _ entities.attrs
    case error e => simp [EvaluateGetAttr.attrsOf_subst_preserves_errors hv₁]
    case ok attrs => simp [Partial.attrsOf] at hv₁
  }
