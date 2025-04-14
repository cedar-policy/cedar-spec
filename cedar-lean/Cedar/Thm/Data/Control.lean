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

theorem do_ok_eq_ok {res : Except ε α} {f : α → β} :
  (do let v ← res ; .ok (f v)) = .ok b ↔
  ∃ a, res = .ok a ∧ f a = b
:= by cases res <;> simp

theorem do_eq_ok {res : Except ε α} {f : α → Except ε β} :
  (do let v ← res ; f v) = .ok b ↔
  ∃ a, res = .ok a ∧ f a = .ok b
:= by cases res <;> simp

theorem do_eq_ok₂ {res₁ res₂: Except ε PUnit} :
  (do res₁ ; res₂) = .ok () → res₁ = .ok () ∧ res₂ = .ok ()
:= by
  cases res₁ <;> cases res₂ <;> simp

theorem to_option_some {v : α} {res: Except ε α} :
  res.toOption = .some v ↔ res = .ok v
:= by
  constructor
  case mp =>
    intro h
    simp [Except.toOption] at h
    split at h <;> simp at h
    subst h
    rfl
  case mpr =>
    intro h
    simp only [Except.toOption, h]

theorem to_option_none {res: Except ε α} :
  res.toOption = .none → (∃ err, res = .error err)
:= by
  intro h
  simp [Except.toOption] at h
  split at h <;> simp at h
  rename_i err
  exists err

theorem to_option_left_ok {α ε₁ ε₂} {v : α} {res₁ : Except ε₁ α} {res₂ : Except ε₂ α} :
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

theorem to_option_right_ok {α ε₁ ε₂} {v : α} {res₁ : Except ε₁ α} {res₂ : Except ε₂ α} :
  res₁.toOption = res₂.toOption → res₂ = .ok v → res₁ = .ok v
:= by
  intro h
  symm at h
  exact to_option_left_ok h

theorem to_option_right_ok' {α ε₁ ε₂} {v : α} {res₁ : Except ε₁ α} :
  res₁.toOption = ((.ok v) : Except ε₂ α).toOption → res₁ = Except.ok v
:= by
  generalize h : ((.ok v) : Except ε₂ α) = res₂
  symm at h
  intro h₁
  exact to_option_right_ok h₁ h

theorem to_option_left_ok' {α ε₁ ε₂} {v : α} {res₂ : Except ε₂ α} :
  ((.ok v) : Except ε₁ α).toOption = res₂.toOption → res₂ = Except.ok v
:= by
  intro h
  symm at h
  exact to_option_right_ok' h

theorem to_option_left_err {ε₁ ε₂ α} {err₁: ε₁} {res₂ : Except ε₂ α} :
  (Except.error err₁).toOption = res₂.toOption → ∃ err₂, res₂ = .error err₂
:= by
  intro h
  simp [Except.toOption] at h
  repeat split at h
  · cases h
  · simp only [Except.error.injEq, exists_eq']

theorem to_option_right_err {ε₂ ε₁ α} {err₂: ε₂} {res₁ : Except ε₁ α} :
  res₁.toOption = (Except.error err₂).toOption → ∃ err₁, res₁ = .error err₁
:= by
  intro h
  symm at h
  exact to_option_left_err h

theorem do_error_to_option {res : Except ε α} {e : ε} :
  (do let (_ : α) ← res ; (.error e : Except ε α)).toOption = .none
:= by
  cases res <;> simp [Except.toOption]
