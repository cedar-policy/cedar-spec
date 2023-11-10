/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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
import Cedar.Thm.Lemmas.Std
import Cedar.Thm.Lemmas.Types
import Cedar.Validation

/-!
This file contains type checker inversion lemmas.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation


theorem type_of_not_inversion {x₁ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.unaryApp .not x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ∃ bty c₁',
    ty = .bool bty.not ∧
    typeOf x₁ c₁ env = Except.ok (.bool bty, c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    rcases res with ⟨ty₁, c₁'⟩
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    case mk.h_1 _ ty₁ bty _ =>
      simp [ok] at h₁
      apply And.intro
      case left => simp [h₁]
      case right =>
        exists bty, c₁'
        simp only [and_true, h₁]

theorem type_of_neg_inversion {x₁ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.unaryApp .neg x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ty = .int ∧
  ∃ c₁', typeOf x₁ c₁ env = Except.ok (.int, c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    rcases res with ⟨ty₁, c₁'⟩
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    simp [ok] at h₁
    simp [h₁]

theorem type_of_mulBy_inversion {x₁ : Expr} {k : Int64} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.unaryApp (.mulBy k) x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ty = .int ∧
  ∃ c₁', typeOf x₁ c₁ env = Except.ok (.int, c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    rcases res with ⟨ty₁, c₁'⟩
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    simp [ok] at h₁
    simp [h₁]

theorem type_of_like_inversion {x₁ : Expr} {p : Pattern} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.unaryApp (.like p) x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ty = .bool .anyBool ∧
  ∃ c₁', typeOf x₁ c₁ env = Except.ok (.string, c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    rcases res with ⟨ty₁, c₁'⟩
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    simp [ok] at h₁
    simp [h₁]

theorem type_of_is_inversion {x₁ : Expr} {ety : EntityType} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.unaryApp (.is ety) x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ∃ ety' c₁',
    ty = (.bool (if ety = ety' then .tt else .ff)) ∧
    typeOf x₁ c₁ env = Except.ok (.entity ety', c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    rcases res with ⟨ty₁, c₁'⟩
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    case mk.h_5 _ _ ety' h₃ =>
      simp only [UnaryOp.is.injEq] at h₃
      subst h₃
      simp [ok] at h₁
      apply And.intro
      case left => simp [h₁]
      case right =>
        exists ety', c₁'
        simp only [h₁, and_self]

end Cedar.Thm
