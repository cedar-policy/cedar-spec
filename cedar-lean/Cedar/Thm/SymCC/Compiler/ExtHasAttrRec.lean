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

module

public import Cedar.SymCC.Compiler
import all Cedar.SymCC.Compiler -- proving things about internals of the compiler

/-!
In this file we prove the equivalence between a recursive and an iterative compilation
function for extended has. The specs use the iterative implementation, which is more
efficient and mirrors the Rust implementation, but the proofs rely on the equivalence
with the recursive implementation (which mimics the recursive compilation of the
desugared form of extended-has).

The only public theorem, at the end of this module, is:
```
compileExtHasAttr_eq_compileExtHasAttrRec (...) :
  compileExtHasAttr t as εs = compileExtHasAttrRec t as εs
```
-/

namespace Cedar.SymCC

open Data Spec Factory

@[expose] public def compileExtHasAttrRec (t : Term) (as : List Attr) (εs : SymEntities) : Result Term :=
  match as with
  | [] => pure (Term.some (Term.prim (.bool true)))
  | [a] => do ifSome t (← compileHasAttr (option.get t) a εs)
  | a :: as₁ => do
    let t₀ ← compileHasAttr (option.get t) a εs
    let t₁ := ifSome t t₀
    match t₁ with
    | .some (.prim (.bool false)) => pure t₁
    | _ =>
      match compileGetAttr (option.get t) a εs with
      | .error .noSuchAttribute => pure t₁
      | .error e => .error e
      | .ok t₂ =>
        let t₄ ← compileExtHasAttrRec (ifSome t t₂) as₁ εs
        compileAnd t₁ (.ok t₄)

end Cedar.SymCC

namespace Cedar.Thm

open Data Spec SymCC

def foldExtHasChecks (results : List Term) : SymCC.Result Term :=
  match results.reverse with
  | [] => pure (Term.some (Term.prim (.bool true)))
  | r :: rs => rs.foldlM (fun result has => compileAnd has (.ok result)) r

theorem foldExtHasChecks_singleton (h : Term) :
  foldExtHasChecks [h] = .ok h := by
  simp only [foldExtHasChecks, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.foldlM_nil, pure, Except.pure]

theorem foldExtHasChecks_cons (h : Term) (rest : List Term) (hne : rest ≠ []) :
  foldExtHasChecks (h :: rest) =
    (foldExtHasChecks rest) >>= (fun result => compileAnd h (.ok result)) := by
  unfold foldExtHasChecks
  cases hr : rest.reverse with
  | nil =>
    exact absurd (List.reverse_eq_nil_iff.mp hr) hne
  | cons r' rs' =>
    simp only [List.reverse_cons, hr, List.cons_append, List.foldlM_cons,
      List.foldlM_append, List.foldlM_nil, bind_pure]

theorem compileExtHasAttr_loop_acc
  (εs : SymEntities) (current : Term) (as : List Attr) (acc : List Term) :
  compileExtHasAttr.loop εs current as acc =
    (compileExtHasAttr.loop εs current as []).map (fun fwd => acc.reverse ++ fwd) := by
  induction as generalizing current acc with
  | nil =>
    unfold compileExtHasAttr.loop
    simp only [List.reverse_nil, List.append_nil, Except.map, List.append_nil]
  | cons a rest ih =>
    rw [compileExtHasAttr.loop, compileExtHasAttr.loop]
    cases hha : compileHasAttr (Factory.option.get current) a εs with
    | error e => simp only [bind, Except.bind, Except.map]
    | ok ht =>
      simp only [bind, Except.bind]
      repeat' split
      all_goals
        try rw [ih (Factory.ifSome current _) (Factory.ifSome current ht :: acc),
                ih (Factory.ifSome current _) [Factory.ifSome current ht]]
      all_goals
        simp only [Except.map, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.append_assoc, List.singleton_append]
      all_goals (repeat' split)
      all_goals simp only []


theorem compileExtHasAttr_eq_loop_fold
  (t : Term) (as : List Attr) (εs : SymEntities) :
  compileExtHasAttr t as εs =
    (compileExtHasAttr.loop εs t as []) >>= foldExtHasChecks := by
  rfl

theorem compileExtHasAttr_loop_nonempty
  (εs : SymEntities) (current : Term) (a : Attr) (rest : List Attr) (acc fwd : List Term)
  (h : compileExtHasAttr.loop εs current (a :: rest) acc = .ok fwd) :
  fwd ≠ [] := by
  rw [compileExtHasAttr.loop] at h
  cases hha : compileHasAttr (Factory.option.get current) a εs with
  | error e => simp only [hha, bind, Except.bind, reduceCtorEq] at h
  | ok ht =>
    simp only [hha, bind, Except.bind] at h
    -- Fully split the `staticallyFalse` match, the `if`, and the `compileGetAttr` match.
    repeat' split at h
    all_goals
      first
      | simp only [reduceCtorEq] at h
      | (injection h with h; subst h; simp)
      | (rw [compileExtHasAttr_loop_acc] at h
         simp only [Except.map] at h
         split at h <;>
           first
           | simp only [reduceCtorEq] at h
           | (injection h with h; subst h
              simp only [ne_eq, List.reverse_cons, List.append_assoc, List.cons_append,
                List.append_eq_nil_iff, List.reverse_eq_nil_iff, List.cons_ne_nil,
                and_false, not_false_eq_true]))

public theorem compileExtHasAttr_eq_compileExtHasAttrRec (t : Term) (as : List Attr) (εs : SymEntities) :
  compileExtHasAttr t as εs = compileExtHasAttrRec t as εs := by
  induction as generalizing t with
  | nil =>
    rw [compileExtHasAttr_eq_loop_fold, compileExtHasAttr.loop, compileExtHasAttrRec]
    simp only [List.reverse_nil, bind, Except.bind, foldExtHasChecks, pure, Except.pure]
  | cons a as' ih =>
    cases as' with
    | nil =>
      rw [compileExtHasAttr_eq_loop_fold, compileExtHasAttr.loop, compileExtHasAttrRec]
      cases hha : compileHasAttr (Factory.option.get t) a εs with
      | error e => simp only [bind, Except.bind]
      | ok ht =>
        simp only [bind, Except.bind, List.isEmpty_nil, Bool.or_true, if_true,
          List.reverse_singleton, foldExtHasChecks_singleton]
    | cons b rest =>
      rw [compileExtHasAttr_eq_loop_fold, compileExtHasAttr.loop]
      simp only [compileExtHasAttrRec]
      cases hha : compileHasAttr (Factory.option.get t) a εs with
      | error e => simp only [bind, Except.bind]
      | ok ht =>
        simp only [bind, Except.bind, List.isEmpty_cons, Bool.or_false]
        by_cases hsf : Factory.ifSome t ht = Term.some (Term.prim (.bool false))
        · simp only [hsf, if_true, List.reverse_singleton, foldExtHasChecks_singleton,
            pure, Except.pure]
        · simp only [Bool.false_eq_true, if_false]
          cases hga : compileGetAttr (Factory.option.get t) a εs with
          | error e =>
            cases e <;> simp only [List.reverse_singleton, foldExtHasChecks_singleton,
              pure, Except.pure]
          | ok t₂ =>
            simp only
            rw [compileExtHasAttr_loop_acc, ← ih (Factory.ifSome t t₂),
              compileExtHasAttr_eq_loop_fold]
            cases hin : compileExtHasAttr.loop εs (Factory.ifSome t t₂) (b :: rest) [] with
            | error e => simp only [Except.map, bind, Except.bind]
            | ok fwd =>
              have hne : fwd ≠ [] :=
                compileExtHasAttr_loop_nonempty εs (Factory.ifSome t t₂) b rest [] fwd hin
              simp only [Except.map, bind, Except.bind, List.reverse_singleton,
                List.singleton_append, foldExtHasChecks_cons _ _ hne]

end Cedar.Thm
