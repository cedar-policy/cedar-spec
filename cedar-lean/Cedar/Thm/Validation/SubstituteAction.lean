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
import Cedar.Thm.Data

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

def SubstituteActionPreservesEvaluation (expr : Expr) (request : Request) (entities : Entities) : Prop :=
  evaluate (substituteAction request.action expr) request entities = evaluate expr request entities

theorem substitute_action_preserves_evaluation_ite {i t e : Expr} {request : Request} {entities : Entities}
  (ih₁ : SubstituteActionPreservesEvaluation i request entities)
  (ih₂ : SubstituteActionPreservesEvaluation t request entities)
  (ih₃ : SubstituteActionPreservesEvaluation e request entities) :
  SubstituteActionPreservesEvaluation (.ite i t e) request entities
:= by
  simp only [SubstituteActionPreservesEvaluation, substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁, ih₂, ih₃]

theorem substitute_action_preserves_evaluation_getAttr {e : Expr} {attr : Attr} {request : Request} {entities : Entities}
(ih₁ : SubstituteActionPreservesEvaluation e request entities) :
  SubstituteActionPreservesEvaluation (.getAttr e attr) request entities
:= by
  simp only [SubstituteActionPreservesEvaluation] at ih₁ ⊢
  simp only [substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁]

theorem substitute_action_preserves_evaluation_hasAttr {e : Expr} {attr : Attr} {request : Request} {entities : Entities}
(ih₁ : SubstituteActionPreservesEvaluation e request entities) :
  SubstituteActionPreservesEvaluation (.hasAttr e attr) request entities
:= by
  simp only [SubstituteActionPreservesEvaluation] at ih₁ ⊢
  simp only [substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁]

theorem substitute_action_preserves_evaluation_unaryApp {op : UnaryOp} {e : Expr} {request : Request} {entities : Entities}
(ih₁ : SubstituteActionPreservesEvaluation e request entities) :
  SubstituteActionPreservesEvaluation (.unaryApp op e) request entities
:= by
  simp only [SubstituteActionPreservesEvaluation] at ih₁ ⊢
  simp only [substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁]

theorem substitute_action_preserves_evaluation_binaryApp {op : BinaryOp} {a b : Expr} {request : Request} {entities : Entities}
(ih₁ : SubstituteActionPreservesEvaluation a request entities)
(ih₂ : SubstituteActionPreservesEvaluation b request entities) :
  SubstituteActionPreservesEvaluation (.binaryApp op a b) request entities
:= by
  simp only [SubstituteActionPreservesEvaluation] at *
  simp only [substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁, ih₂]

theorem substitute_action_preserves_evaluation_and {a b : Expr} {request : Request} {entities : Entities}
(ih₁ : SubstituteActionPreservesEvaluation a request entities)
(ih₂ : SubstituteActionPreservesEvaluation b request entities) :
  SubstituteActionPreservesEvaluation (.and a b) request entities
:= by
  simp only [SubstituteActionPreservesEvaluation, substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁, ih₂]

theorem substitute_action_preserves_evaluation_or {a b : Expr} {request : Request} {entities : Entities}
(ih₁ : SubstituteActionPreservesEvaluation a request entities)
(ih₂ : SubstituteActionPreservesEvaluation b request entities) :
  SubstituteActionPreservesEvaluation (.or a b) request entities
:= by
  simp only [SubstituteActionPreservesEvaluation, substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁, ih₂]

theorem substitute_action_nil_set : ∀ (uid : EntityUID),
  substituteAction uid (.set []) = .set []
:= by
  intro uid
  simp only [substituteAction, mapOnVars, List.attach_def, List.pmap, List.map_nil]

theorem substitute_action_cons_set : ∀ (h : Expr) (t : List Expr) (uid : EntityUID),
  substituteAction uid (.set (h :: t)) = .set ((substituteAction uid h) :: t.map (substituteAction uid))
:= by
  intro h t uid
  simp only [substituteAction, mapOnVars, List.attach_def, List.map_pmap_subtype, List.map_cons]
  simp only [Expr.set.injEq, List.cons.injEq, true_and]
  unfold substituteAction
  simp only

theorem substitute_action_preserves_evaluation_set {xs : List Expr} {request : Request} {entities : Entities}
(ih₁ : ∀ xᵢ ∈ xs,  SubstituteActionPreservesEvaluation xᵢ request entities) :
  SubstituteActionPreservesEvaluation (.set xs) request entities
:= by
  unfold SubstituteActionPreservesEvaluation
  cases h₀ : xs with
  | nil =>
    rw [substitute_action_nil_set]
  | cons h t =>
    have ⟨h₁, h₂⟩ :
      SubstituteActionPreservesEvaluation h request entities ∧
      ∀ x ∈ t, SubstituteActionPreservesEvaluation x request entities
    := by simpa [h₀] using ih₁
    replace h₂ := List.mapM_congr h₂
    rw [substitute_action_cons_set]
    simp only [evaluate, List.mapM₁, List.attach_def, List.mapM_pmap_subtype (fun x => evaluate x request entities)]
    simp only [List.mapM_cons, List.mapM_map]
    rw [h₁, h₂]

theorem substitute_action_nil_record : ∀ (uid : EntityUID),
  substituteAction uid (.record []) = .record []
:= by
  intro uid
  simp only [substituteAction, mapOnVars, List.attach₂, List.pmap, List.map_nil]

theorem substitute_action_cons_record : ∀ (ax : Attr × Expr) (axs : List (Attr × Expr)) (uid : EntityUID),
  substituteAction uid (.record (ax :: axs)) =
  .record ((ax.fst, substituteAction uid ax.snd) :: axs.map (fun (a, e) => (a, substituteAction uid e)))
:= by
  intro h t uid
  simp only [substituteAction, mapOnVars, List.attach₂, List.map_pmap_subtype_snd, List.map_cons]

theorem substitute_action_preserves_evaluation_record {axs : List (Attr × Expr)} {request : Request} {entities : Entities}
(ih₁ : ∀ axᵢ ∈ axs, SubstituteActionPreservesEvaluation axᵢ.snd request entities) :
  SubstituteActionPreservesEvaluation (.record axs) request entities
:= by
  unfold SubstituteActionPreservesEvaluation
  cases h₀ : axs with
  | nil =>
    rw [substitute_action_nil_record]
  | cons hd tl =>
    have ⟨h₁, h₂⟩ :
      SubstituteActionPreservesEvaluation hd.snd request entities ∧
      ∀ ax ∈ tl, SubstituteActionPreservesEvaluation ax.snd request entities
    := by simpa [h₀] using ih₁
    replace h₂ : ∀ ax ∈ tl,
      (do pure (ax.fst,←evaluate (substituteAction request.action ax.snd) request entities)) =
      (do pure (ax.fst,←evaluate ax.snd request entities)) := by simpa using h₂
    replace h₂ := List.mapM_congr h₂
    rw [substitute_action_cons_record]
    simp only [evaluate, List.mapM₂, List.attach₂, List.mapM_pmap_subtype (fun (a, e) => bindAttr a (evaluate e request entities))]
    simp only [bindAttr, List.mapM_map, List.mapM_cons]
    rw [h₁, h₂]

theorem substitute_action_nil_call : ∀ (uid : EntityUID) (xfn : ExtFun),
  substituteAction uid (.call xfn []) = .call xfn [] :=
by
  intro uid
  simp only [substituteAction, mapOnVars, List.attach_def, List.pmap, List.map_nil, implies_true]


theorem substitute_action_cons_call : ∀ (x : Expr) (xs : List Expr) (uid : EntityUID) (xfn : ExtFun),
  substituteAction uid (.call xfn (x :: xs)) = .call xfn ((substituteAction uid x) :: xs.map (substituteAction uid)) :=
by
  intro h t uid
  simp only [substituteAction, mapOnVars, List.attach_def, List.map_pmap_subtype, List.map_cons]
  simp only [Expr.call.injEq, List.cons.injEq, true_and, forall_const]
  unfold substituteAction
  simp only


theorem substitute_action_preserves_evaluation_call {xfn : ExtFun} {xs : List Expr} {request : Request} {entities : Entities}
(ih₁ : ∀ xᵢ, xᵢ ∈ xs → SubstituteActionPreservesEvaluation xᵢ request entities) :
  SubstituteActionPreservesEvaluation (.call xfn xs) request entities
:= by
  unfold SubstituteActionPreservesEvaluation
  cases h₀ : xs with
  | nil =>
    rw [substitute_action_nil_call]
  | cons h t =>
    have ⟨h₁, h₂⟩ :
      SubstituteActionPreservesEvaluation h request entities ∧
      ∀ x ∈ t, SubstituteActionPreservesEvaluation x request entities
    := by simpa [h₀] using ih₁
    replace h₂ := List.mapM_congr h₂
    rw [substitute_action_cons_call]
    simp only [evaluate, List.mapM₁, List.attach_def, List.mapM_pmap_subtype (fun x => evaluate x request entities)]
    simp only [List.mapM_cons, List.mapM_map]
    rw [h₁, h₂]

theorem substitute_action_preserves_evaluation (expr : Expr) (request : Request) (entities : Entities) :
  evaluate (substituteAction request.action expr) request entities =
  evaluate expr request entities
:= by
  cases h₀ : expr with
  | lit p => simp only [substituteAction, mapOnVars]
  | var vr =>
    cases vr <;> simp only [substituteAction, mapOnVars] <;> try assumption
    case action =>
      simp [evaluate]
  | ite i t e =>
    have ih₁ := substitute_action_preserves_evaluation i request entities
    have ih₂ := substitute_action_preserves_evaluation t request entities
    have ih₃ := substitute_action_preserves_evaluation e request entities
    exact @substitute_action_preserves_evaluation_ite i t e request entities ih₁ ih₂ ih₃
  | and a b =>
    have ih₁ := substitute_action_preserves_evaluation a request entities
    have ih₂ := substitute_action_preserves_evaluation b request entities
    exact @substitute_action_preserves_evaluation_and a b request entities ih₁ ih₂
  | or a b =>
    have ih₁ := substitute_action_preserves_evaluation a request entities
    have ih₂ := substitute_action_preserves_evaluation b request entities
    exact @substitute_action_preserves_evaluation_or a b request entities ih₁ ih₂
  | unaryApp op e =>
    have ih₁ := substitute_action_preserves_evaluation e request entities
    exact @substitute_action_preserves_evaluation_unaryApp op e request entities ih₁
  | binaryApp op a b =>
    have ih₁ := substitute_action_preserves_evaluation a request entities
    have ih₂:= substitute_action_preserves_evaluation b request entities
    exact @substitute_action_preserves_evaluation_binaryApp op a b request entities ih₁ ih₂
  | getAttr x attr =>
    have ih₁ := substitute_action_preserves_evaluation x request entities
    exact @substitute_action_preserves_evaluation_getAttr x attr request entities ih₁
  | hasAttr x attr =>
    have ih₁ := substitute_action_preserves_evaluation x request entities
    exact @substitute_action_preserves_evaluation_hasAttr x attr request entities ih₁
  | set xs =>
    have ih : ∀ xᵢ, xᵢ ∈ xs → SubstituteActionPreservesEvaluation xᵢ request entities := by
      intro xᵢ _
      exact @substitute_action_preserves_evaluation xᵢ request entities
    exact @substitute_action_preserves_evaluation_set xs request entities ih
  | record axs =>
    have ih : ∀ axᵢ, axᵢ ∈ axs → SubstituteActionPreservesEvaluation axᵢ.snd request entities := by
      intro axᵢ hᵢ
      have _ : sizeOf axᵢ.snd < 1 + sizeOf axs := by
        apply List.sizeOf_snd_lt_sizeOf_list hᵢ
      exact @substitute_action_preserves_evaluation axᵢ.snd request entities
    exact @substitute_action_preserves_evaluation_record axs request entities ih
  | call xfn xs =>
    have ih : ∀ xᵢ, xᵢ ∈ xs → SubstituteActionPreservesEvaluation xᵢ request entities := by
      intro xᵢ _
      exact @substitute_action_preserves_evaluation xᵢ request entities
    exact @substitute_action_preserves_evaluation_call xfn xs request entities ih

theorem substitute_action_preserves_evaluates_to {expr : Expr} {request : Request} {entities : Entities} {v : Value}:
  EvaluatesTo (substituteAction request.action expr) request entities v ↔
  EvaluatesTo expr request entities v
:= by simp only [EvaluatesTo, substitute_action_preserves_evaluation]

end Cedar.Thm
