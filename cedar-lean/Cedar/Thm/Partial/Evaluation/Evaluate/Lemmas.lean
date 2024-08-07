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

import Cedar.Partial.Value
import Cedar.Thm.Data.List
import Cedar.Thm.Data.LT

/-!
  This file contains lemmas about `mapM` and `SortedBy` that seem a little too
  specialized to go in `Thm/Data`, particularly because one of them uses
  `Partial.Value`.
-/

namespace Cedar.Thm.Partial.Evaluation.Evaluate

open Cedar.Data
open Cedar.Spec (Attr)

theorem mapM_Option_on_snd_preserves_sortedBy_fst [LT α] [DecidableLT α] [StrictLT α] {abs : List (α × β)} {f : β → Option γ} :
  abs.SortedBy Prod.fst →
  abs.mapM (λ (a, b) => do some (a, ← f b)) = some ags →
  ags.SortedBy Prod.fst
:= by
  intro h₁ h₂
  replace h₂ := List.mapM_some_eq_filterMap h₂
  subst h₂
  apply List.filterMap_sortedBy _ h₁
  simp only [Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, implies_true]

theorem mapM_Except_on_snd_preserves_sortedBy_fst [LT α] [DecidableLT α] [StrictLT α] {abs : List (α × β)} {f : β → Except ε γ} :
  abs.SortedBy Prod.fst →
  abs.mapM (λ (a, b) => do .ok (a, ← f b)) = .ok ags →
  ags.SortedBy Prod.fst
:= by
  intro h₁ h₂
  replace h₂ := List.mapM_ok_eq_filterMap h₂
  subst h₂
  apply List.filterMap_sortedBy _ h₁
  intro (a, b) (a', g)
  split <;> rename_i h₂ <;> split at h₂ <;> rename_i h₃
  <;> simp only [Prod.mk.injEq] at h₃ <;> replace ⟨h₃, h₃'⟩ := h₃ <;> subst h₃ h₃'
  · simp only [Option.some.injEq]
    cases hb : f b <;> simp only [hb, Except.bind_err, Except.bind_ok, Except.ok.injEq] at h₂
    subst h₂
    simp only [Prod.mk.injEq, and_imp]
    intro _ ; subst a' ; simp only [implies_true]
  · simp only [false_implies]

/--
  Not quite a pure specialization of the above to a particular `f`, because the
  lambda has a different shape
-/
theorem mapM_Option_on_snd_preserves_sortedBy_fst' {avs : List (Attr × Partial.Value)} :
  avs.SortedBy Prod.fst →
  avs.mapM (λ av => match av.snd with | .value v => some (av.fst, v) | .residual _ => none) = some ags →
  ags.SortedBy Prod.fst
:= by
  intro h₁ h₂
  replace h₂ := List.mapM_some_eq_filterMap h₂
  subst h₂
  apply List.filterMap_sortedBy _ h₁
  intro (a₁, pv) (a₂, v)
  split <;> simp
  · intro h₁ _ ; exact h₁

end Cedar.Thm.Partial.Evaluation.Evaluate
