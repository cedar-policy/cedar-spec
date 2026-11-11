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

import CedarGen.Relational.Depth.Step
import Specimen.Correctness.Workers

/-! # Linearly bounded depth of the derived expression generator

An expression the derived `HasType` generator produces is at most `D iS sz` deeper than the
capabilities it starts from: linear in the size `sz` for a fixed leaf size `iS`. -/

namespace Cedar.Validation.Relational.Depth

open Cedar.Spec Cedar.Validation Cedar.Data Specimen.Correctness
open Cedar.Validation.Relational.ExprGen.RequestVars

/-- At fuel `0` the workers produce nothing. -/
theorem bound_zero : Bound 0 :=
  ⟨fun iS sz decl syn c env ty => by simp only [hasTypeGen]; rw [(worker% gen HasType [2, 6] eq_zero)]; walk,
    fun iS sz decl syn c env ty => by simp only [extCallGen]; rw [(worker% gen HasTypeExtCall [2, 3] eq_zero)]; walk,
    fun iS sz decl syn c env tys => by simp only [listGen]; rw [(worker% gen HasTypeList [2] eq_zero)]; walk,
    fun iS sz decl syn b c env rty => by simp only [recordOfGen]; rw [(worker% gen RecordTypeOf [3] eq_zero)]; walk,
    fun iS sz decl syn c env => by simp only [fieldsGen]; rw [(worker% gen HasTypeFields [2, 5] eq_zero)]; walk,
    fun iS sz decl syn c env => by simp only [hasTypeTyGen]; rw [(worker% gen HasType [2, 5, 6] eq_zero)]; walk,
    fun iS sz decl syn c env => by simp only [extCallTyGen]; rw [(worker% gen HasTypeExtCall [2, 3, 6] eq_zero)]; walk,
    fun iS sz decl syn b c env => by simp only [recordOfTyGen]; rw [(worker% gen RecordTypeOf [3, 6] eq_zero)]; walk,
    fun iS sz decl syn lb c env => by simp only [recordTyGen]; rw [(worker% gen HasTypeRecord [3, 6] eq_zero)]; walk,
    fun iS sz decl syn lb c env atys => by simp only [recordGen]; rw [(worker% gen HasTypeRecord [3] eq_zero)]; walk⟩

theorem bound_all : ∀ fuel, Bound fuel
  | 0 => bound_zero
  | fuel + 1 => have ih := bound_all fuel
    ⟨stepHasType fuel ih,
     stepExtCall fuel ih,
     stepList fuel ih,
     stepRecordOf fuel ih,
     stepFields fuel ih,
     stepHasTypeTy fuel ih,
     stepExtCallTy fuel ih,
     stepRecordOfTy fuel ih,
     stepRecordTy fuel ih,
     stepRecord fuel ih⟩

/-- **Linearly bounded expression depth.** An expression the derived `HasType` generator produces
    (at any fuel, size `sz` and leaf size `iS`, from the capabilities `c`) is at most
    `D iS sz = sz · (iS + 2)` deeper than `c`, and so are the capabilities it earns. -/
theorem hasType_gen_depth {fuel iS sz : Nat} {decl syn : Bool} {c : Capabilities} {env : TypeEnv}
    {ty : CedarType} {x : Expr} {cout : Capabilities}
    (h : Produces ((worker% gen HasType [2, 6] (G := SGen)) fuel iS sz decl syn c env ty) (x, cout)) :
    exprDepth x ≤ D iS sz + capsDepth c ∧ capsDepth cout ≤ D iS sz + capsDepth c := by
  have h₁ := (bound_all fuel).1 iS sz decl syn c env ty (x, cout) h
  have h₂ := capsHasType fuel iS sz decl syn c env ty (x, cout) h
  simp only at h₁ h₂
  omega

/-- From no capabilities (a policy condition), the depth is at most `D iS sz`. -/
theorem hasType_gen_depth_nil {fuel iS sz : Nat} {decl syn : Bool} {env : TypeEnv} {ty : CedarType}
    {x : Expr} {cout : Capabilities}
    (h : Produces ((worker% gen HasType [2, 6] (G := SGen)) fuel iS sz decl syn [] env ty) (x, cout)) :
    exprDepth x ≤ D iS sz := by
  simpa [capsDepth] using (hasType_gen_depth h).1

/-- The same, for the generator as an instance: `BacktrackGenFor.gen s l` runs the worker at size
    `s` and leaf size `l`. -/
theorem hasType_instance_gen_depth {decl syn : Bool} {c : Capabilities} {env : TypeEnv}
    {ty : CedarType} {s l : Nat} {x : Expr} {cout : Capabilities}
    (h : Produces (BacktrackGenFor.gen (P := fun (p : Expr × Capabilities) => match p with
        | (x, cout) => HasType decl syn x c env ty cout) (G := SGen) s l) (x, cout)) :
    exprDepth x ≤ D l s + capsDepth c :=
  (hasType_gen_depth h).1

theorem D_eq (iS sz : Nat) : D iS sz = sz * (iS + 2) := rfl

#print axioms hasType_gen_depth
#print axioms hasType_gen_depth_nil
#print axioms hasType_instance_gen_depth

end Cedar.Validation.Relational.Depth
