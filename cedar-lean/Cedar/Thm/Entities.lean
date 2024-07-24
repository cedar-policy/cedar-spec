
import Batteries.Data.List
import Cedar.Spec.Entities
import Cedar.Data.Map
namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec


def subslice (e₁ e₂ : Entities) : Prop :=
  ∀ (euid : EntityUID) (edata),
    e₁.find? euid = some edata →
    e₁.find? euid = e₂.find? euid

theorem subslice_refl (e : Entities) :
  subslice e e
  := by
  simp [subslice]

theorem subslice_trans (e₁ e₂ e₃ : Entities)
  (h₁ : subslice e₁ e₂)
  (h₂ : subslice e₂ e₃) :
  subslice e₁ e₃
  := by
  simp [subslice] at *
  intros euid edata h
  have step₁ : Map.find? e₁ euid = Map.find? e₂ euid := by
    apply h₁
    apply h
  have step₂ : Map.find? e₂ euid = Map.find? e₃ euid := by
    apply h₂
    rw [← step₁]
    apply h
  simp [step₁, step₂]

end Cedar.Thm
