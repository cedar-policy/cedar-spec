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

import CedarGen.Relational.Depth.Facts
import Specimen.Correctness.Workers

/-! The depth budget, and the statement each step of the fuel induction proves. -/

namespace Cedar.Validation.Relational.Depth

open Cedar.Spec Cedar.Validation Cedar.Data Specimen.Correctness
open Cedar.Validation.Relational.ExprGen.RequestVars

noncomputable abbrev hasTypeGen : ℕ → ℕ → ℕ → Bool → Bool → Capabilities → TypeEnv → CedarType → SGen (Expr × Capabilities) :=
  (worker% gen HasType [2, 6])
noncomputable abbrev extCallGen : ℕ → ℕ → ℕ → Bool → Bool → Capabilities → TypeEnv → CedarType → SGen (ExtFun × List Expr) :=
  (worker% gen HasTypeExtCall [2, 3])
noncomputable abbrev listGen : ℕ → ℕ → ℕ → Bool → Bool → Capabilities → TypeEnv → List CedarType → SGen (List Expr) :=
  (worker% gen HasTypeList [2])
noncomputable abbrev recordOfGen : ℕ → ℕ → ℕ → Bool → Bool → Bool → Capabilities → TypeEnv → RecordType → SGen (List (Attr × Expr)) :=
  (worker% gen RecordTypeOf [3])
noncomputable abbrev fieldsGen : ℕ → ℕ → ℕ → Bool → Bool → Capabilities → TypeEnv → SGen (List (Attr × Expr) × List (Attr × QualifiedType)) :=
  (worker% gen HasTypeFields [2, 5])
noncomputable abbrev hasTypeTyGen : ℕ → ℕ → ℕ → Bool → Bool → Capabilities → TypeEnv → SGen (Expr × CedarType × Capabilities) :=
  (worker% gen HasType [2, 5, 6])
noncomputable abbrev extCallTyGen : ℕ → ℕ → ℕ → Bool → Bool → Capabilities → TypeEnv → SGen (ExtFun × List Expr × CedarType) :=
  (worker% gen HasTypeExtCall [2, 3, 6])
noncomputable abbrev recordOfTyGen : ℕ → ℕ → ℕ → Bool → Bool → Bool → Capabilities → TypeEnv → SGen (List (Attr × Expr) × RecordType) :=
  (worker% gen RecordTypeOf [3, 6])
noncomputable abbrev recordTyGen : ℕ → ℕ → ℕ → Bool → Bool → Option Attr → Capabilities → TypeEnv → SGen (List (Attr × Expr) × List (Attr × QualifiedType)) :=
  (worker% gen HasTypeRecord [3, 6])
noncomputable abbrev recordGen : ℕ → ℕ → ℕ → Bool → Bool → Option Attr → Capabilities → TypeEnv → List (Attr × QualifiedType) → SGen (List (Attr × Expr)) :=
  (worker% gen HasTypeRecord [3])

/-- The depth budget at a size, `sz · (iS + 2)`. A size step adds a node over a call at the
    smaller size (two, for an action literal in a set of entity literals), or `1 + |as| ≤ iS + 1`
    for an `e has a.as` (`ExtHasIf` draws `as` at the leaf size), or a node over a skipped operand,
    which `anyExpr iS` draws, of depth at most `iS`. A split into halves (thirds) whose second
    call starts from capabilities the first earned, and so may copy its subexpressions, at most
    doubles: `2 · D iS (n / 2) + 1 ≤ D iS (n + 1)`. -/
def D (iS sz : Nat) : Nat := sz * (iS + 2)

theorem D_facts (iS n : Nat) :
    D iS (n + 1) = D iS n + (iS + 2) ∧ 2 * D iS (n / 2) ≤ D iS n ∧ 3 * D iS (n / 3) ≤ D iS n ∧
    D iS (n / 2) ≤ D iS n ∧ D iS (n / 3) ≤ D iS n := by
  have m2 : 2 * (n / 2 * (iS + 2)) ≤ n * (iS + 2) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.mul_div_le n 2)
  have m3 : 3 * (n / 3 * (iS + 2)) ≤ n * (iS + 2) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.mul_div_le n 3)
  have h1 : (n + 1) * (iS + 2) = n * (iS + 2) + (iS + 2) := by rw [Nat.add_mul, Nat.one_mul]
  have h2 : n / 2 * (iS + 2) ≤ n * (iS + 2) := Nat.mul_le_mul_right _ (Nat.div_le_self n 2)
  have h3 : n / 3 * (iS + 2) ≤ n * (iS + 2) := Nat.mul_le_mul_right _ (Nat.div_le_self n 3)
  simp only [D]
  omega

theorem D_zero (iS : Nat) : D iS 0 = 0 := by simp [D]

def HasTypeBound (fuel : Nat) : Prop :=
  ∀ iS sz decl syn c env ty, succObs.spec (hasTypeGen fuel iS sz decl syn c env ty) (fun v => exprDepth v.1 ≤ D iS sz + capsDepth c)

def ExtCallBound (fuel : Nat) : Prop :=
  ∀ iS sz decl syn c env ty, succObs.spec (extCallGen fuel iS sz decl syn c env ty) (fun v => listDepth v.2 ≤ D iS sz + capsDepth c)

def ListBound (fuel : Nat) : Prop :=
  ∀ iS sz decl syn c env tys, succObs.spec (listGen fuel iS sz decl syn c env tys) (fun v => listDepth v ≤ D iS sz + capsDepth c)

def RecordOfBound (fuel : Nat) : Prop :=
  ∀ iS sz decl syn b c env rty, succObs.spec (recordOfGen fuel iS sz decl syn b c env rty) (fun v => recDepth v ≤ D iS sz + capsDepth c)

def FieldsBound (fuel : Nat) : Prop :=
  ∀ iS sz decl syn c env, succObs.spec (fieldsGen fuel iS sz decl syn c env) (fun v => recDepth v.1 ≤ D iS sz + capsDepth c)

def HasTypeTyBound (fuel : Nat) : Prop :=
  ∀ iS sz decl syn c env, succObs.spec (hasTypeTyGen fuel iS sz decl syn c env) (fun v => exprDepth v.1 ≤ D iS sz + capsDepth c)

def ExtCallTyBound (fuel : Nat) : Prop :=
  ∀ iS sz decl syn c env, succObs.spec (extCallTyGen fuel iS sz decl syn c env) (fun v => listDepth v.2.1 ≤ D iS sz + capsDepth c)

def RecordOfTyBound (fuel : Nat) : Prop :=
  ∀ iS sz decl syn b c env, succObs.spec (recordOfTyGen fuel iS sz decl syn b c env) (fun v => recDepth v.1 ≤ D iS sz + capsDepth c)

def RecordTyBound (fuel : Nat) : Prop :=
  ∀ iS sz decl syn lb c env, succObs.spec (recordTyGen fuel iS sz decl syn lb c env) (fun v => recDepth v.1 ≤ D iS sz + capsDepth c)

def RecordBound (fuel : Nat) : Prop :=
  ∀ iS sz decl syn lb c env atys, succObs.spec (recordGen fuel iS sz decl syn lb c env atys) (fun v => recDepth v ≤ D iS sz + capsDepth c)

/-- The depth bound at one fuel level, for every worker of the expression-producing block. -/
def Bound (fuel : Nat) : Prop :=
  HasTypeBound fuel ∧
  ExtCallBound fuel ∧
  ListBound fuel ∧
  RecordOfBound fuel ∧
  FieldsBound fuel ∧
  HasTypeTyBound fuel ∧
  ExtCallTyBound fuel ∧
  RecordOfTyBound fuel ∧
  RecordTyBound fuel ∧
  RecordBound fuel

theorem capsHasType (fuel iS sz decl syn c env ty) :
    succObs.spec (hasTypeGen fuel iS sz decl syn c env ty) (fun v => capsDepth v.2 ≤ max (exprDepth v.1) (capsDepth c)) :=
  succ_mono ((worker% gen HasType [2, 6] sound) fuel iS sz decl syn c env ty) fun _ h => HasType.capsDepth_le h

theorem capsHasTypeTy (fuel iS sz decl syn c env) :
    succObs.spec (hasTypeTyGen fuel iS sz decl syn c env) (fun v => capsDepth v.2.2 ≤ max (exprDepth v.1) (capsDepth c)) :=
  succ_mono ((worker% gen HasType [2, 5, 6] sound) fuel iS sz decl syn c env) fun _ h => HasType.capsDepth_le h

theorem succ_and {α : Type} {g : SGen α} {P Q : α → Prop} (h₁ : succObs.spec g P) (h₂ : succObs.spec g Q) :
    succObs.spec g (fun v => P v ∧ Q v) := fun v hv => ⟨h₁ v hv, h₂ v hv⟩

/-- Close a walk's leaf: unfold the depths, add the budget's arithmetic, and `omega`. -/
macro "depth_leaf" i:term:max n:term:max : tactic => `(tactic| (
  try simp only [listDepth, recDepth, exprDepth, capsDepth, keyDepth, List.length_cons,
    List.length_nil, nat_div_eq_div] at *
  have := D_facts $i $n
  have := D_zero $i
  first
  | omega
  | (simp_all only [listDepth, recDepth, exprDepth, capsDepth, keyDepth]; omega)
  | (casesm* _ × _
     simp only [listDepth, recDepth, exprDepth, capsDepth, keyDepth] at *
     omega)))

/-- One fuel step of `Bound`, for whichever worker the goal is about: open it, walk with the bounds
`ih` gives at fuel `f` (and what each callee is known to produce), and close the leaves by
arithmetic. A callee no fact mentions is passed over (`add_trivial_succ_facts`). -/
macro "depth_step " f:term:max ih:term:max : tactic => `(tactic| (
  obtain ⟨iHasType, iExtCall, iList, iRecordOf, iFields, iHasTypeTy, iExtCallTy, iRecordOfTy, iRecordTy, iRecord⟩ := $ih
  have oHasType := fun iS sz decl syn c env ty =>
    succ_and (iHasType iS sz decl syn c env ty) (capsHasType $f iS sz decl syn c env ty)
  have oHasTypeTy := fun iS sz decl syn c env =>
    succ_and (iHasTypeTy iS sz decl syn c env) (capsHasTypeTy $f iS sz decl syn c env)
  clear iHasType iHasTypeTy
  simp only [HasTypeBound, ExtCallBound, ListBound, RecordOfBound, FieldsBound, HasTypeTyBound, ExtCallTyBound, RecordOfTyBound, RecordTyBound,
    RecordBound, hasTypeGen, extCallGen, listGen, recordOfGen, fieldsGen, hasTypeTyGen, extCallTyGen, recordOfTyGen, recordTyGen,
    recordGen] at *
  intro iS sz
  intros
  cases sz with
  | zero =>
    unfold_worker_step
    unfold_gen_instances
    add_trivial_succ_facts
    walk [oHasType, iExtCall, iList, iRecordOf, iFields, oHasTypeTy, iExtCallTy, iRecordOfTy, iRecordTy, iRecord, @capTagMem_depth, @capMerge_depth, @extHasAttrChain_depth, @extHasAttrChainBool_depth, @hasAttrInRecord_depth, @hasAttrInRecordTy_depth, @extHasIf_depth, @capIntersect_depth, @isActionLitMemSet_depth, @sortsTo_depth, @deadOperand_depth, @validDecimal_gen, @validIP_gen, @validDatetime_gen, @validDuration_gen]
    clear_trivial_gen_facts
    all_goals depth_leaf iS 0
  | succ n =>
    unfold_worker_step
    unfold_gen_instances
    add_trivial_succ_facts
    walk [oHasType, iExtCall, iList, iRecordOf, iFields, oHasTypeTy, iExtCallTy, iRecordOfTy, iRecordTy, iRecord, @capTagMem_depth, @capMerge_depth, @extHasAttrChain_depth, @extHasAttrChainBool_depth, @hasAttrInRecord_depth, @hasAttrInRecordTy_depth, @extHasIf_depth, @capIntersect_depth, @isActionLitMemSet_depth, @sortsTo_depth, @deadOperand_depth, @validDecimal_gen, @validIP_gen, @validDatetime_gen, @validDuration_gen]
    clear_trivial_gen_facts
    all_goals depth_leaf iS n))

end Cedar.Validation.Relational.Depth
