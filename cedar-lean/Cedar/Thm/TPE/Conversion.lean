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
import Cedar.Thm.TPE.Soundness
import Cedar.Thm.Validation.WellTyped.Definition
import Cedar.Thm.Validation.WellTyped.ResidualDefinition
import Cedar.Thm.Data.List.Lemmas

/-!
This file defines the main theorem of TPE soundness and its associated lemmas.
-/

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation

set_option pp.proofs true

mutual
theorem conversion_preserves_evaluation_forall2 :
  List.Forall₂ (fun x y => Spec.evaluate x.toExpr req es = (TypedExpr.toResidual y).evaluate req es) ls ls := by
  cases ls with
  | nil =>
    simp
  | cons head tail =>
    simp
    constructor
    case left =>
      apply conversion_preserves_evaluation
    case right =>
      apply conversion_preserves_evaluation_forall2

theorem conversion_preserves_evaluation_forall2_map {map : List (Attr × TypedExpr)} :
  List.Forall₂
  (fun x y =>
    Prod.mk x.fst <$> Spec.evaluate x.snd.toExpr req es =
      Prod.mk y.fst <$> (TypedExpr.toResidual y.snd).evaluate req es)
  map map := by
  cases map with
  | nil =>
    simp
  | cons head tail =>
    simp
    constructor
    case left =>
      apply conversion_preserves_evaluation
    case right =>
      apply conversion_preserves_evaluation_forall2_map



/--
Theorem stating that converting a TypedExpr to a Residual preserves evaluation semantics.
That is, evaluating the original TypedExpr (converted to Expr) gives the same result
as evaluating the converted Residual.
-/
theorem conversion_preserves_evaluation (te : TypedExpr) (req : Request) (es : Entities) :
  Spec.evaluate te.toExpr req es = (TypedExpr.toResidual te).evaluate req es := by
  cases te with
  | lit p ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
  | var v ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual]
    cases v <;> simp [Spec.evaluate, Residual.evaluate]
  | ite cond thenExpr elseExpr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_cond := conversion_preserves_evaluation cond req es
    have ih_then := conversion_preserves_evaluation thenExpr req es
    have ih_else := conversion_preserves_evaluation elseExpr req es
    rw [←ih_cond]
    simp [Result.as, Value.asBool]
    rw [←ih_then, ←ih_else]
    cases Spec.evaluate cond.toExpr req es
    case ite.error =>
      simp
    case ite.ok =>
      simp
      rename_i a
      cases a
      case prim =>
        simp [bind, Coe.coe, Value.asBool]
      all_goals {
        simp [Coe.coe, Value.asBool]
      }
  | and a b ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_a := conversion_preserves_evaluation a req es
    have ih_b := conversion_preserves_evaluation b req es
    rw [←ih_a, ←ih_b]
  | or a b ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_a := conversion_preserves_evaluation a req es
    have ih_b := conversion_preserves_evaluation b req es
    rw [←ih_a, ←ih_b]
  | unaryApp op expr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih := conversion_preserves_evaluation expr req es
    rw [←ih]
  | binaryApp op a b ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_a := conversion_preserves_evaluation a req es
    have ih_b := conversion_preserves_evaluation b req es
    rw [←ih_a, ←ih_b]
  | getAttr expr attr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih := conversion_preserves_evaluation expr req es
    rw [←ih]
  | hasAttr expr attr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih := conversion_preserves_evaluation expr req es
    rw [←ih]
  | set ls ty =>
    unfold TypedExpr.toExpr
    simp [TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    congr 1
    rw [List.map₁_eq_map, List.map₁_eq_map]


    dsimp only [List.attachWith, List.mapM₁, List.attach, List.attach₂, List.mapM₂, List.mapM₁, List.map₁, List.attach]
    rw [List.mapM_pmap_subtype (fun x => Spec.evaluate x req es)]
    rw [List.mapM_pmap_subtype (fun x => x.evaluate req es) (List.map TypedExpr.toResidual ls) (List.attach._proof_1 (List.map TypedExpr.toResidual ls))]

    rw [List.mapM_map, List.mapM_map]
    rw [List.forall₂_implies_mapM_eq]
    apply conversion_preserves_evaluation_forall2
  | record map ty =>
    unfold TypedExpr.toExpr
    simp [TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    congr 1

    dsimp only [List.attachWith, List.mapM₁, List.attach, List.attach₂, List.mapM₂, List.mapM₁, List.map₁, List.attach]
    rw [List.mapM_pmap_subtype (fun x => bindAttr x.fst (Spec.evaluate x.snd req es)) (List.map (fun x => (x.1.fst, x.1.snd.toExpr)) (List.pmap Subtype.mk map fun x => List.sizeOf_snd_lt_sizeOf_list))]
    rw [List.map_pmap_subtype (fun x => (x.fst, x.snd.toExpr)) map]
    rw [List.map_pmap_subtype (fun x => (x.fst, TypedExpr.toResidual x.snd)) map]
    rw [List.mapM_pmap_subtype (fun x => bindAttr x.fst (x.snd.evaluate req es)) (List.map (fun x => (x.fst, TypedExpr.toResidual x.snd)) map)]
    unfold bindAttr
    rw [List.mapM_map, List.mapM_map]
    simp
    rw [List.forall₂_implies_mapM_eq]
    apply conversion_preserves_evaluation_forall2_map
  | call xfn args ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    congr 1
    dsimp only [List.attachWith, List.mapM₁, List.attach, List.attach₂, List.mapM₂, List.mapM₁, List.map₁, List.attach]
    rw [List.map_pmap_subtype]
    rw [List.map_pmap_subtype]
    rw [List.mapM_pmap_subtype (fun x => x.evaluate req es) (List.map TypedExpr.toResidual args)]
    rw [List.mapM_pmap_subtype (fun x => Spec.evaluate x req es)]
    rw [List.mapM_map, List.mapM_map]
    rw [List.forall₂_implies_mapM_eq]
    apply conversion_preserves_evaluation_forall2
end


theorem conversion_preserves_typeof (e: TypedExpr) :
  TypedExpr.typeOf e = Residual.typeOf (TypedExpr.toResidual e) := by
  cases e
  all_goals {
    simp [TypedExpr.toResidual, Residual.typeOf, TypedExpr.typeOf]
  }

theorem conversion_preserves_typedness:
  TypedExpr.WellTyped env expr →
    Residual.WellTyped env (TypedExpr.toResidual expr) := by
  intro h
  cases expr with
  | lit p ty' =>
    simp [TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.val
    cases h with
    | lit h₁ =>
      -- Convert Prim.WellTyped to InstanceOfType
      cases h₁ with
      | bool b =>
        apply InstanceOfType.instance_of_bool
        simp [InstanceOfBoolType]
      | int i =>
        apply InstanceOfType.instance_of_int
      | string s =>
        apply InstanceOfType.instance_of_string
      | entityUID uid h₁ =>
        apply InstanceOfType.instance_of_entity
        simp [InstanceOfEntityType]
        unfold EntityUID.WellFormed
        exact h₁
  | var v ty' =>
    simp [TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.var
    cases h with
    | var h₁ => exact h₁
  | ite x₁ x₂ x₃ ty' =>
    simp [TypedExpr.toResidual] at h ⊢
    cases h with
    | ite h₁ h₂ h₃ h₄ h₅ =>
      rw [conversion_preserves_typeof x₂]
      apply Residual.WellTyped.ite
      · apply conversion_preserves_typedness
        exact h₁
      · apply conversion_preserves_typedness
        exact h₂
      · apply conversion_preserves_typedness
        exact h₃
      · rw [←conversion_preserves_typeof x₁]
        exact h₄
      · rw [←conversion_preserves_typeof x₂, ←conversion_preserves_typeof x₃]
        exact h₅
  | and x₁ x₂ ty' =>
    simp [TypedExpr.toResidual] at h ⊢
    cases h with
    | and h₁ h₂ h₃ h₄ =>
      apply Residual.WellTyped.and
      · apply conversion_preserves_typedness
        exact h₁
      · apply conversion_preserves_typedness
        exact h₂
      · rw [←conversion_preserves_typeof x₁]
        exact h₃
      · rw [←conversion_preserves_typeof x₂]
        exact h₄
  | or x₁ x₂ ty' =>
    simp [TypedExpr.toResidual] at h ⊢
    cases h with
    | or h₁ h₂ h₃ h₄ =>
      apply Residual.WellTyped.or
      · apply conversion_preserves_typedness
        exact h₁
      · apply conversion_preserves_typedness
        exact h₂
      · rw [←conversion_preserves_typeof x₁]
        exact h₃
      · rw [←conversion_preserves_typeof x₂]
        exact h₄
  | unaryApp op₁ x₁ ty' =>
    simp [TypedExpr.toResidual] at h ⊢
    cases h with
    | unaryApp h₁ h₂ =>
      apply Residual.WellTyped.unaryApp
      · apply conversion_preserves_typedness
        exact h₁
      · -- Convert UnaryOp.WellTyped to UnaryResidualWellTyped
        cases h₂ with
        | not h₂ =>
          apply UnaryResidualWellTyped.not
          rw [←conversion_preserves_typeof x₁]
          exact h₂
        | neg h₂ =>
          apply UnaryResidualWellTyped.neg
          rw [←conversion_preserves_typeof x₁]
          exact h₂
        | isEmpty h₂ =>
          apply UnaryResidualWellTyped.isEmpty
          rw [←conversion_preserves_typeof x₁]
          exact h₂
        | like h₂ =>
          apply UnaryResidualWellTyped.like
          rw [←conversion_preserves_typeof x₁]
          exact h₂
        | is h₂ =>
          apply UnaryResidualWellTyped.is
          rw [←conversion_preserves_typeof x₁]
          exact h₂
  | binaryApp op₂ x₁ x₂ ty' =>
    simp [TypedExpr.toResidual] at h ⊢
    cases h with
    | binaryApp h₁ h₂ h₃ =>
      apply Residual.WellTyped.binaryApp
      · apply conversion_preserves_typedness
        exact h₁
      · apply conversion_preserves_typedness
        exact h₂
      · -- Convert BinaryOp.WellTyped to BinaryResidualWellTyped
        cases h₃ with
        | eq_lit =>
          simp [TypedExpr.toResidual]
          apply BinaryResidualWellTyped.eq_val
        | eq_entity h₃ h₄ =>
          apply BinaryResidualWellTyped.eq_entity
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
        | eq h₃ =>
          apply BinaryResidualWellTyped.eq
          rw [←conversion_preserves_typeof x₁, ←conversion_preserves_typeof x₂]
          exact h₃
        | memₑ h₃ h₄ =>
          apply BinaryResidualWellTyped.memₑ
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
        | memₛ h₃ h₄ =>
          apply BinaryResidualWellTyped.memₛ
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
        | less_int h₃ h₄ =>
          apply BinaryResidualWellTyped.less_int
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
        | less_datetime h₃ h₄ =>
          apply BinaryResidualWellTyped.less_datetime
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
        | less_duration h₃ h₄ =>
          apply BinaryResidualWellTyped.less_duration
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
        | lessEq_int h₃ h₄ =>
          apply BinaryResidualWellTyped.lessEq_int
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
        | lessEq_datetime h₃ h₄ =>
          apply BinaryResidualWellTyped.lessEq_datetime
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
        | lessEq_duration h₃ h₄ =>
          apply BinaryResidualWellTyped.lessEq_duration
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
        | add h₃ h₄ =>
          apply BinaryResidualWellTyped.add
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
        | sub h₃ h₄ =>
          apply BinaryResidualWellTyped.sub
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
        | mul h₃ h₄ =>
          apply BinaryResidualWellTyped.mul
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
        | contains h₃ =>
          apply BinaryResidualWellTyped.contains
          rw [←conversion_preserves_typeof x₁, ←conversion_preserves_typeof x₂]
          exact h₃
        | containsAll h₃ h₄ =>
          apply BinaryResidualWellTyped.containsAll
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
        | containsAny h₃ h₄ =>
          apply BinaryResidualWellTyped.containsAny
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
        | hasTag h₃ h₄ =>
          apply BinaryResidualWellTyped.hasTag
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
        | getTag h₃ h₄ h₅ =>
          apply BinaryResidualWellTyped.getTag
          · rw [←conversion_preserves_typeof x₁]
            exact h₃
          · rw [←conversion_preserves_typeof x₂]
            exact h₄
          · exact h₅
  | getAttr x₁ attr ty' =>
    simp [TypedExpr.toResidual] at h ⊢
    cases h with
    | getAttr_entity h₁ h₂ h₃ h₄ =>
      apply Residual.WellTyped.getAttr_entity
      · apply conversion_preserves_typedness
        exact h₁
      · rw [←conversion_preserves_typeof x₁]
        exact h₂
      · exact h₃
      · exact h₄
    | getAttr_record h₁ h₂ h₃ =>
      apply Residual.WellTyped.getAttr_record
      · apply conversion_preserves_typedness
        exact h₁
      · rw [←conversion_preserves_typeof x₁]
        exact h₂
      · exact h₃
  | hasAttr x₁ attr ty' =>
    simp [TypedExpr.toResidual] at h ⊢
    cases h with
    | hasAttr_entity h₁ h₂ =>
      apply Residual.WellTyped.hasAttr_entity
      · apply conversion_preserves_typedness
        exact h₁
      · rw [←conversion_preserves_typeof x₁]
        exact h₂
    | hasAttr_record h₁ h₂ =>
      apply Residual.WellTyped.hasAttr_record
      · apply conversion_preserves_typedness
        exact h₁
      · rw [←conversion_preserves_typeof x₁]
        exact h₂
  | set ls ty' =>
    simp [TypedExpr.toResidual] at h ⊢
    cases h with
    | set h₁ h₂ h₃ =>
      dsimp only [List.attachWith, List.mapM₁, List.attach, List.attach₂, List.mapM₂, List.mapM₁, List.map₁, List.attach]
      rw [List.map_pmap_subtype (fun x => TypedExpr.toResidual x)]
      apply Residual.WellTyped.set
      · intro x hx
        simp [List.mem_map] at hx
        rcases hx with ⟨y, hy, hxy⟩
        rw [←hxy]
        apply conversion_preserves_typedness
        exact h₁ y hy
      · intro x hx
        simp [List.mem_map] at hx
        rename_i ty
        rcases hx with ⟨y, hy, hxy⟩
        rw [←hxy]
        specialize h₁ y hy
        rw [← conversion_preserves_typeof y]
        specialize h₂ y hy
        exact h₂
      · cases ls with
        | nil => simp at h₃
        | cons => simp
  | record m ty' =>
    simp [TypedExpr.toResidual] at h ⊢
    cases h with
    | record h₁ h₂ =>
      dsimp only [List.attachWith, List.mapM₁, List.attach, List.attach₂, List.mapM₂, List.mapM₁, List.map₁, List.attach]
      rw [List.map_pmap_subtype (fun x => (x.fst, TypedExpr.toResidual x.snd)) m]
      apply Residual.WellTyped.record
      · intro k v hkv
        simp [List.mem_map] at hkv
        rcases hkv with ⟨a, ⟨b, ⟨inm, ⟨aeqk, btov⟩⟩⟩⟩
        rw [←btov]
        apply conversion_preserves_typedness
        exact h₁ a b inm
      · simp [h₂]
        congr 1
        ext ⟨k, v⟩
        simp [conversion_preserves_typeof]
        simp
        constructor
        . intro h
          rcases h with ⟨a, ⟨b, ⟨h₁, h₂⟩⟩⟩
          exists a
          exists b
          constructor
          . exact h₁
          . rw [← conversion_preserves_typeof b]
            exact h₂
        . intro h
          rcases h with ⟨a, ⟨b, ⟨h₁, h₂⟩⟩⟩
          exists a
          exists b
          constructor
          . exact h₁
          . rw [conversion_preserves_typeof b]
            exact h₂
  | call xfn args ty' =>
    simp [TypedExpr.toResidual] at h ⊢
    cases h with
    | call h₁ h₂ =>
      dsimp only [List.attachWith, List.mapM₁, List.attach, List.attach₂, List.mapM₂, List.mapM₁, List.map₁, List.attach]
      rw [List.map_pmap_subtype (fun x => TypedExpr.toResidual x)]
      apply Residual.WellTyped.call
      · intro x hx
        simp [List.mem_map] at hx
        rcases hx with ⟨y, hy, hxy⟩
        rw [←hxy]
        apply conversion_preserves_typedness
        exact h₁ y hy
      · -- Convert ExtFun.WellTyped to ExtResidualWellTyped
        cases h₂ with
        | decimal h₂ =>
          simp [TypedExpr.toResidual]
          apply ExtResidualWellTyped.decimal
          exact h₂
        | lessThan h₂ h₃ =>
          apply ExtResidualWellTyped.lessThan
          · rw [←conversion_preserves_typeof]
            exact h₂
          · rw [←conversion_preserves_typeof]
            exact h₃
        | lessThanOrEqual h₂ h₃ =>
          apply ExtResidualWellTyped.lessThanOrEqual
          · rw [←conversion_preserves_typeof]
            exact h₂
          · rw [←conversion_preserves_typeof]
            exact h₃
        | greaterThan h₂ h₃ =>
          apply ExtResidualWellTyped.greaterThan
          · rw [←conversion_preserves_typeof]
            exact h₂
          · rw [←conversion_preserves_typeof]
            exact h₃
        | greaterThanOrEqual h₂ h₃ =>
          apply ExtResidualWellTyped.greaterThanOrEqual
          · rw [←conversion_preserves_typeof]
            exact h₂
          · rw [←conversion_preserves_typeof]
            exact h₃
        | ip h₂ =>
          simp [TypedExpr.toResidual]
          apply ExtResidualWellTyped.ip
          exact h₂
        | isIpv4 h₂ =>
          apply ExtResidualWellTyped.isIpv4
          rw [←conversion_preserves_typeof]
          exact h₂
        | isIpv6 h₂ =>
          apply ExtResidualWellTyped.isIpv6
          rw [←conversion_preserves_typeof]
          exact h₂
        | isLoopback h₂ =>
          apply ExtResidualWellTyped.isLoopback
          rw [←conversion_preserves_typeof]
          exact h₂
        | isMulticast h₂ =>
          apply ExtResidualWellTyped.isMulticast
          rw [←conversion_preserves_typeof]
          exact h₂
        | isInRange h₂ h₃ =>
          apply ExtResidualWellTyped.isInRange
          · rw [←conversion_preserves_typeof]
            exact h₂
          · rw [←conversion_preserves_typeof]
            exact h₃
        | datetime h₂ =>
          simp [TypedExpr.toResidual]
          apply ExtResidualWellTyped.datetime
          exact h₂
        | duration h₂ =>
          simp [TypedExpr.toResidual]
          apply ExtResidualWellTyped.duration
          exact h₂
        | offset h₂ h₃ =>
          apply ExtResidualWellTyped.offset
          · rw [←conversion_preserves_typeof]
            exact h₂
          · rw [←conversion_preserves_typeof]
            exact h₃
        | durationSince h₂ h₃ =>
          apply ExtResidualWellTyped.durationSince
          · rw [←conversion_preserves_typeof]
            exact h₂
          · rw [←conversion_preserves_typeof]
            exact h₃
        | toDate h₂ =>
          apply ExtResidualWellTyped.toDate
          rw [←conversion_preserves_typeof]
          exact h₂
        | toTime h₂ =>
          apply ExtResidualWellTyped.toTime
          rw [←conversion_preserves_typeof]
          exact h₂
        | toMilliseconds h₂ =>
          apply ExtResidualWellTyped.toMilliseconds
          rw [←conversion_preserves_typeof]
          exact h₂
        | toSeconds h₂ =>
          apply ExtResidualWellTyped.toSeconds
          rw [←conversion_preserves_typeof]
          exact h₂
        | toMinutes h₂ =>
          apply ExtResidualWellTyped.toMinutes
          rw [←conversion_preserves_typeof]
          exact h₂
        | toHours h₂ =>
          apply ExtResidualWellTyped.toHours
          rw [←conversion_preserves_typeof]
          exact h₂
        | toDays h₂ =>
          apply ExtResidualWellTyped.toDays
          rw [←conversion_preserves_typeof]
          exact h₂
termination_by sizeOf expr
decreasing_by
  all_goals (
    simp
    rename_i a b d d _e _f _g _ _i _j _k _l _m _n _o
    (first
     | rename_i p r _s; rw [r]; simp; omega
     | rename_i p q r s t u _v; rw [s]; simp; omega
     | rw [a]; simp; omega
     | rw [b]; simp; omega
     | rw [d]; simp; omega
     | skip)
  )
  . rw [d]
    simp
    let h := List.sizeOf_lt_of_mem hy
    omega
  . rename_i p q r _s
    rw [r]
    simp
    let h := List.sizeOf_lt_of_mem inm
    simp at h
    omega
  . rw [b]
    simp
    let h := List.sizeOf_lt_of_mem hy
    simp at h
    omega

end Cedar.Thm
