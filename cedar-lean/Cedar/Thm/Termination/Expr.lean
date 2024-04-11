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

import Cedar.Spec.Expr

namespace Cedar.Spec

open Cedar.Data

def Expr.size : Expr -> Nat
  | .lit _ => 1
  | .var _ => 1
  | .ite x₁ x₂ x₃ => 1 + x₁.size + x₂.size + x₃.size
  | .and x₁ x₂ => 1 + x₁.size + x₂.size
  | .or x₁ x₂ => 1 + x₁.size + x₂.size
  | .unaryApp _ x₁ => 1 + x₁.size
  | .binaryApp _ x₁ x₂ => 1 + x₁.size + x₂.size
  | .getAttr x₁ _ => 1 + x₁.size
  | .hasAttr x₁ _ => 1 + x₁.size
  | .set xs => 1 + (xs.map Expr.size).foldl Nat.add 0
  | .record m => 1 + (m.map (Expr.size ∘ Prod.snd)).foldl Nat.add 0
  | .call _ xs => 1 + (xs.map Expr.size).foldl Nat.add 0
decreasing_by all_goals sorry

def Expr.ite_termination {x₁ x₂ x₃ : Expr} :
  x₁.size < (Expr.ite x₁ x₂ x₃).size ∧
  x₂.size < (Expr.ite x₁ x₂ x₃).size ∧
  x₃.size < (Expr.ite x₁ x₂ x₃).size
:= by
  repeat (any_goals (apply And.intro))
  all_goals {
    conv => rhs ; unfold size
    omega
  }

def Expr.and_termination {x₁ x₂ : Expr} :
  x₁.size < (Expr.and x₁ x₂).size ∧
  x₂.size < (Expr.and x₁ x₂).size
:= by
  apply And.intro
  all_goals {
    conv => rhs ; unfold size
    omega
  }

def Expr.or_termination {x₁ x₂ : Expr} :
  x₁.size < (Expr.or x₁ x₂).size ∧
  x₂.size < (Expr.or x₁ x₂).size
:= by
  apply And.intro
  all_goals {
    conv => rhs ; unfold size
    omega
  }

def Expr.unaryApp_termination {x₁ : Expr} {op : UnaryOp} :
  x₁.size < (Expr.unaryApp op x₁).size
:= by
  conv => rhs ; unfold size
  omega

def Expr.binaryApp_termination {x₁ x₂ : Expr} {op : BinaryOp} :
  x₁.size < (Expr.binaryApp op x₁ x₂).size ∧
  x₂.size < (Expr.binaryApp op x₁ x₂).size
:= by
  apply And.intro
  all_goals {
    conv => rhs ; unfold size
    omega
  }

def Expr.getAttr_termination {x₁ : Expr} {attr : Attr} :
  x₁.size < (Expr.getAttr x₁ attr).size
:= by
  conv => rhs ; unfold size
  omega

def Expr.hasAttr_termination {x₁ : Expr} {attr : Attr} :
  x₁.size < (Expr.hasAttr x₁ attr).size
:= by
  conv => rhs ; unfold size
  omega

def Expr.set_termination {xs : List Expr} :
  ∀ x ∈ xs, x.size < (Expr.set xs).size
:= by
  intro x h₁
  conv => rhs ; unfold size
  sorry

def Expr.record_termination {pairs : List (Attr × Expr)} :
  ∀ kv ∈ pairs, kv.snd.size < (Expr.record pairs).size
:= by
  intro kv h₁
  conv => rhs ; unfold size
  sorry

def Expr.call_termination {xs : List Expr} {xfn : ExtFun} :
  ∀ x ∈ xs, x.size < (Expr.call xfn xs).size
:= by
  intro x h₁
  conv => rhs ; unfold size
  sorry

end Cedar.Spec
