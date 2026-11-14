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

import CedarGen.Relational.ExprGen
import Specimen.Correctness.GenInterpSPMF
import Aesop

/-! Depth of expressions, and the capability lemma: what `HasType` adds to the capabilities is no
deeper than the expression it types, or than what was there already. -/

set_option linter.unusedSimpArgs false

namespace Cedar.Validation.Relational.Depth

open Cedar.Spec Cedar.Validation Cedar.Data

mutual
/-- Depth of an expression. `e has a.b.c` counts its implicit `getAttr` chain. -/
def exprDepth : Expr → Nat
  | .lit _ | .var _ => 0
  | .ite a b c => max (exprDepth a) (max (exprDepth b) (exprDepth c)) + 1
  | .and a b | .or a b | .binaryApp _ a b => max (exprDepth a) (exprDepth b) + 1
  | .unaryApp _ a | .getAttr a _ | .hasAttr a _ => exprDepth a + 1
  | .extHasAttr a _ as => exprDepth a + as.length + 1
  | .set xs | .call _ xs => listDepth xs + 1
  | .record axs => recDepth axs + 1
def listDepth : List Expr → Nat
  | [] => 0
  | x :: xs => max (exprDepth x) (listDepth xs)
def recDepth : List (Attr × Expr) → Nat
  | [] => 0
  | (_, x) :: r => max (exprDepth x) (recDepth r)
end

def keyDepth : Key → Nat
  | .attr _ => 0
  | .tag e => exprDepth e

def capsDepth : Capabilities → Nat
  | [] => 0
  | (x, k) :: c => max (max (exprDepth x) (keyDepth k)) (capsDepth c)

theorem capsDepth_append (a b : Capabilities) :
    capsDepth (a ++ b) = max (capsDepth a) (capsDepth b) := by
  induction a with
  | nil => simp [capsDepth]
  | cons p a ih => obtain ⟨x, k⟩ := p; simp only [List.cons_append, capsDepth, ih]; omega

theorem CapMerge.capsDepth_le {a b c : Capabilities} (h : CapMerge a b c) :
    capsDepth c ≤ max (capsDepth a) (capsDepth b) := by
  induction h <;> simp only [capsDepth] at * <;> omega

theorem capsDepth_filter (p : Expr × Key → Bool) (c : Capabilities) :
    capsDepth (c.filter p) ≤ capsDepth c := by
  induction c with
  | nil => simp [capsDepth]
  | cons q c ih => obtain ⟨x, k⟩ := q; by_cases hp : p (x, k) <;> simp [List.filter, hp, capsDepth] <;> omega

theorem capsDepth_capIntersect (a b : Capabilities) : capsDepth (capIntersect a b) ≤ capsDepth a :=
  capsDepth_filter _ a

theorem HasAttrInRecord.capsDepth_le {rty x a c k b ci}
    (h : HasAttrInRecord rty x a c k b ci) : capsDepth ci ≤ exprDepth x := by
  cases h <;> simp [capsDepth, keyDepth]

theorem HasAttrOn.capsDepth_le {env ty x a c b ci}
    (h : HasAttrOn env ty x a c b ci) : capsDepth ci ≤ exprDepth x := by
  cases h <;> first | exact HasAttrInRecord.capsDepth_le ‹_› | simp [capsDepth]

theorem ExtHasAttrChain.capsDepth_le {env ty x a as c b cout}
    (h : ExtHasAttrChain env ty x a as c b cout) : capsDepth cout ≤ exprDepth x + as.length := by
  induction h with
  | last _ _ _ _ _ _ h => exact Nat.le_trans (HasAttrOn.capsDepth_le h) (Nat.le_add_right _ _)
  | absent _ _ _ _ _ _ _ h => exact Nat.le_trans (HasAttrOn.capsDepth_le h) (Nat.le_add_right _ _)
  | restFf => simp [capsDepth]
  | restTt _ x _ _ _ _ _ _ _ _ _ _ hha _ _ _ _ hm2 ih =>
    have h1 := HasAttrOn.capsDepth_le hha; have h2 := CapMerge.capsDepth_le hm2
    simp only [exprDepth, List.length_cons] at ih ⊢; omega
  | restAnyBool _ x _ _ _ _ _ _ _ _ _ _ hha _ _ _ _ hm2 ih =>
    have h1 := HasAttrOn.capsDepth_le hha; have h2 := CapMerge.capsDepth_le hm2
    simp only [exprDepth, List.length_cons] at ih ⊢; omega

open Lean Elab Tactic Meta in
/-- Add the depth bound of every capability-producing hypothesis to the context. -/
elab "depth_facts" : tactic => withMainContext do
  let lemmas : List (Lean.Name × Lean.Name) :=
    [(``Cedar.Validation.Relational.CapMerge, ``Cedar.Validation.Relational.Depth.CapMerge.capsDepth_le), (``Cedar.Validation.Relational.HasAttrOn, ``Cedar.Validation.Relational.Depth.HasAttrOn.capsDepth_le),
     (``Cedar.Validation.Relational.HasAttrInRecord, ``Cedar.Validation.Relational.Depth.HasAttrInRecord.capsDepth_le),
     (``Cedar.Validation.Relational.ExtHasAttrChain, ``Cedar.Validation.Relational.Depth.ExtHasAttrChain.capsDepth_le)]
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars ldecl.type)
    let some fn := ty.getAppFn.constName? | continue
    let some (_, l) := lemmas.find? (·.1 == fn) | continue
    let pf ← mkAppM l #[ldecl.toExpr]
    let pty ← inferType pf
    liftMetaTactic fun g => do
      let g ← g.assert (← mkFreshUserName `hd) pty pf
      let (_, g) ← g.intro1P
      pure [g]

set_option maxHeartbeats 4000000 in
/-- What `HasType` adds to the capabilities is no deeper than the expression it types, or than
    the capabilities it started from. -/
theorem HasType.capsDepth_le {decl syn x c env ty cout} (h : HasType decl syn x c env ty cout) :
    capsDepth cout ≤ max (exprDepth x) (capsDepth c) := by
  induction h using HasType.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True) (motive_6 := fun _ _ _ _ _ => True)
  all_goals intros
  all_goals first
    | trivial
    | (simp only [capsDepth]; omega)
    | (depth_facts;
       simp only [exprDepth, capsDepth, keyDepth, capsDepth_append, List.length_cons, id] at *; omega)
    | (depth_facts; refine Nat.le_trans (capsDepth_capIntersect _ _) ?_;
       simp only [exprDepth, capsDepth, keyDepth, capsDepth_append, List.length_cons, id] at *; omega)

end Cedar.Validation.Relational.Depth
