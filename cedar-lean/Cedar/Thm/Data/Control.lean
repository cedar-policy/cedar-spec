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


/-!
This file contains `simp` lemmas for proofs about code that uses the `do`
notation together with `Except` and `Option`.
-/


-- The `Except.bind_*` theorems let `simp` reduce terms that use the `do` notation.
@[simp] theorem Except.bind_ok_T (a : α) (f : α → ExceptT ε Id β) :
  (bind (Except.ok a) f : ExceptT ε Id β) = f a
:= by rfl

@[simp] theorem Except.bind_ok (a : α) (f : α → Except ε β) :
  (bind (Except.ok a) f : Except ε β) = f a
:= by rfl

@[simp] theorem Except.bind_err (e : ε) (f : α → Except ε β) :
  (bind (Except.error e) f : Except ε β) = (Except.error e)
:= by rfl

-- The `Option.bind_*` theorems let `simp` reduce terms that use the `do` notation.
@[simp] theorem Option.bind_some_T (a : α) (f : α → OptionT Id β) :
  (bind (Option.some a) f : OptionT Id β) = f a
:= by rfl

@[simp] theorem Option.bind_some_fun (a : α) (f : α → Option β) :
  (bind (Option.some a) f : Option β) = f a
:= by rfl

@[simp] theorem Option.bind_none_fun (f : α → Option β) :
  (bind Option.none f : Option β) = Option.none
:= by rfl

theorem do_some {opt : Option α} {f : α → β} :
  (do let v ← opt ; some (f v)) = some b ↔
  ∃ a, opt = some a ∧ f a = b
:= by cases opt <;> simp

theorem do_error {res : Except ε α} {e : ε} {f : α → β} :
  (do let v ← res ; .ok (f v)) = .error e ↔
  res = .error e
:= by cases res <;> simp

theorem do_ok {res : Except ε α} {f : α → β} :
  (do let v ← res ; .ok (f v)) = .ok b ↔
  ∃ a, res = .ok a ∧ f a = b
:= by cases res <;> simp

theorem to_option_left_ok {v : α} {res₁ res₂ : Except ε α} :
  res₁.toOption = res₂.toOption → res₁ = .ok v → res₂ = .ok v
:= by
  intro h₀ h₁
  simp [Except.toOption] at h₀
  repeat split at h₀
  · simp only [Except.ok.injEq]
    simp only [Option.some.injEq] at h₀
    simp only [Except.ok.injEq] at h₁
    simp only [← h₀]; exact h₁
  · cases h₀
  · cases h₁

theorem to_option_left_err {err₁: ε} {res₁ res₂ : Except ε α} :
  res₁.toOption = res₂.toOption → res₁ = .error err₁ → ∃ err₂, res₂ = .error err₂
:= by
  intro h₀ h₁
  simp [Except.toOption] at h₀
  repeat split at h₀
  · cases h₁
  · cases h₁
  · split at h₀
    · cases h₀
    · simp only [Except.error.injEq] at h₁
      simp only [Except.error.injEq, exists_eq']
