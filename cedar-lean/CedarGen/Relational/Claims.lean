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

import CedarGen.Relational.Depth.ExprDepth
import CedarGen.Relational.Sound.SchemaTwoTypes
import CedarGen.Relational.Sound.SchemaVariety
import CedarGen.Relational.Sound.SparseHierarchy

/-! # What the Cedar generators produce

The properties of the derived schema and expression generators, stated with the usual notation for
probability. Each is a restatement of a theorem in `Sound` or `Depth`.

A generator is a subdistribution over its results: a run can fail, so probabilities and means are
over the runs that succeed. `x ∈ supp g` says `g` can produce `x`. -/

namespace Cedar.Validation.Relational.Claims

open Cedar.Spec Cedar.Validation Cedar.Validation.Relational Cedar.Validation.Relational.Schema
open Cedar.Validation.Relational.SchemaGen Cedar.Validation.Relational.Depth
open Cedar.Validation.Relational.ExprGen.RequestVars
open Specimen.Correctness Basalt ENNReal

variable {α : Type}

/-! ## Notation -/

/-- What `g` can produce. -/
def supp (g : SGen α) : Set α := {x | Produces g x}

/-- The probability that `g` produces a value satisfying `E`. -/
noncomputable def prob (g : SGen α) (E : α → Prop) : ℝ≥0∞ := sprob g {x | E x}

/-- The probability that `g` produces a value satisfying `E`, given that it satisfies `C`. -/
noncomputable def condProb (g : SGen α) (E C : α → Prop) : ℝ≥0∞ :=
  prob g (fun x => C x ∧ E x) / prob g C

/-- The mean of `f` over what `g` produces, given `C`. -/
noncomputable def condMean (g : SGen α) (f : α → ℝ≥0∞) (C : α → Prop) : ℝ≥0∞ :=
  sexpect g ({x | C x}.indicator f) / prob g C

/-- `Pr[x ← g : E x]`, `Pr[x ← g : E x | C x]`, `𝔼[x ← g : f x | C x]`; `x` may be a pattern. -/
syntax "Pr[" term " ← " term " : " term "]" : term
@[inherit_doc prob] syntax "Pr[" term " ← " term " : " term " | " term "]" : term
@[inherit_doc condMean] syntax "𝔼[" term " ← " term " : " term " | " term "]" : term
/-- `Pr[g succeeds]`: the probability that a run of `g` succeeds. -/
syntax "Pr[" term " succeeds" "]" : term

macro_rules
  | `(Pr[$x ← $g : $E]) => `(prob $g fun y => match y with | $x => $E)
  | `(Pr[$x ← $g : $E | $C]) =>
    `(condProb $g (fun y => match y with | $x => $E) (fun y => match y with | $x => $C))
  | `(𝔼[$x ← $g : $f | $C]) =>
    `(condMean $g (fun y => match y with | $x => $f) (fun y => match y with | $x => $C))
  | `(Pr[$g succeeds]) => `(sok $g)

/-! ## The generators -/

/-- The schema generator with budget `b`, at size `s` and leaf size `l`. It produces a type
environment `Γ`, and the mode `m` (flat, sparse or dense) it built `Γ`'s entity hierarchy in. -/
noncomputable abbrev schemaGen (b s l : Nat) : SGen (HierMode × TypeEnv) :=
  BacktrackGenFor.gen (P := fun p : HierMode × TypeEnv => GenTypeEnvB p.1 b p.2) (G := SGen) s l

/-- The expression generator at size `n` and leaf size `l`: expressions `e` of type `τ` in `Γ`, with
the capabilities `c` in scope, together with the capabilities `c'` that `e` earns. -/
noncomputable abbrev exprGen (decl syn : Bool) (c : Capabilities) (Γ : TypeEnv) (τ : CedarType) (n l : Nat) :
    SGen (Expr × Capabilities) :=
  BacktrackGenFor.gen (P := fun (p : Expr × Capabilities) => match p with
    | (e, c') => HasType decl syn e c Γ τ c') (G := SGen) n l

/-- `Γ`'s standard entity types, each with its ancestors. -/
def hierarchy (Γ : TypeEnv) : List (EntityType × List EntityType) := Sound.standardPairs Γ.ets.toList

/-- The mean, over `Γ`'s standard entity types, of how many ancestors each has. -/
noncomputable def meanAncestors (Γ : TypeEnv) : ℝ :=
  ((hierarchy Γ).map (fun t => t.2.length)).sum / (hierarchy Γ).length

/-! ## Unfolding the notation -/

theorem prob_le_one (g : SGen α) (E : α → Prop) : prob g E ≤ 1 :=
  sexpect_le_one g fun a => by unfold Set.indicator; split <;> simp

theorem ancStats_eq : ∀ es : List (EntityType × EntitySchemaEntry),
    Sound.ancStats es = (((Sound.standardPairs es).map (fun t => t.2.length)).sum,
      (Sound.standardPairs es).length)
  | [] => rfl
  | (_, .standard e) :: rest => by
    simp [Sound.ancStats, Sound.standardPairs, ancStats_eq rest, Nat.add_comm]
  | (_, .enum _) :: rest => by simp only [Sound.ancStats, Sound.standardPairs, ancStats_eq rest]

theorem meanAncestors_eq (Γ : TypeEnv) : meanAncestors Γ = Sound.meanAnc Γ.ets.toList := by
  simp only [meanAncestors, hierarchy, Sound.meanAnc, ancStats_eq]
  split <;> simp_all

/-! ## The claims -/

/-- **Sparse hierarchies are forests.** In a schema generated in the sparse mode, every entity
type has no ancestors, or a parent `p` followed by `p`'s own ancestors. -/
theorem sparse_hierarchy_forest (b s l : Nat) (Γ : TypeEnv) (h : (.sparse, Γ) ∈ supp (schemaGen b s l)) :
    ∀ t ∈ hierarchy Γ, t.2 = [] ∨ ∃ p ps, t.2 = p :: ps ∧ (p, ps) ∈ hierarchy Γ :=
  Sound.generated_sparse_forest _ _ _ b Γ.ets.1 Γ.acts Γ.reqty h

/-- **The mean number of ancestors is logarithmic.** In a schema generated in the sparse mode, an
entity type has on average at most `ln (l + 1)` ancestors. -/
theorem sparse_mean_ancestors (b s l : Nat) :
    𝔼[(m, Γ) ← schemaGen b s l : .ofReal (meanAncestors Γ) | m = .sparse ∧ hierarchy Γ ≠ []]
      ≤ .ofReal (Real.log (l + 1)) := by
  refine ENNReal.div_le_of_le_mul ?_
  have h := Sure.genTypeEnvB_instance_sparse_mean_log b s l
  convert h using 2
  · funext ⟨m, Γ⟩
    simp only [Set.indicator, Set.mem_ofPred_eq, meanAncestors_eq]
    by_cases hr : m = .sparse
    · by_cases hh : hierarchy Γ = []
      · simp only [hierarchy] at hh
        simp [hr, hh, Sound.meanAnc, ancStats_eq]
      · simp [hr, hh]
    · simp [hr]
  · simp only [prob, hierarchy, ancStats_eq, Nat.one_le_iff_ne_zero, ne_eq, List.length_eq_zero_iff]

/-- **Expression depth is linear.** A generated expression is at most `n (l + 2)` deeper than the
capabilities in scope, that is, than the attribute checks that enclose it. -/
theorem expr_depth (decl syn : Bool) (c : Capabilities) (Γ : TypeEnv) (τ : CedarType) (n l : Nat)
    (e : Expr) (c' : Capabilities) (h : (e, c') ∈ supp (exprGen decl syn c Γ τ n l)) :
    exprDepth e ≤ n * (l + 2) + capsDepth c :=
  hasType_instance_gen_depth (decl := decl) (syn := syn) (env := Γ) (ty := τ) (cout := c') h

/-- **Schemas are well formed.** Every generated schema is a well-formed type environment. -/
theorem schema_well_formed (b s l : Nat) (m : HierMode) (Γ : TypeEnv)
    (h : (m, Γ) ∈ supp (schemaGen b s l)) : WfTypeEnv Γ :=
  (Sound.genTypeEnvB_instance_generated b s l m Γ h).1

/-- **At most `b` type combinations.** Every generated schema has at most `b` request
environments. -/
theorem schema_combinations (b s l : Nat) (m : HierMode) (Γ : TypeEnv)
    (h : (m, Γ) ∈ supp (schemaGen b s l)) : Γ.schema.environments.length ≤ b :=
  (Sound.genTypeEnvB_instance_generated b s l m Γ h).2

/-- **The schema generator never fails** when its budget allows a request environment. -/
theorem schema_never_fails (b s l : Nat) (hb : 1 ≤ b) : Pr[schemaGen b s l succeeds] = 1 := by
  simpa [hb] using Sure.genTypeEnvB_instance_sok b s l

/-- **Schemas are varied.** With a budget of at least two and a leaf size of at least one, a generated
schema with at least two entity types (which has positive probability) has at least two request
environments with probability at least `5/18`. -/
theorem schema_varied (b s l : Nat) (hb : 2 ≤ b) (hl : 1 ≤ l) :
    Pr[(_, Γ) ← schemaGen b s l : 2 ≤ Γ.schema.environments.length | 2 ≤ Γ.ets.toList.length]
      ≥ 5 / 18 := by
  have hpos : Pr[(_, Γ) ← schemaGen b s l : 2 ≤ Γ.ets.toList.length] ≠ 0 :=
    Sure.genTypeEnvB_instance_two_types b s l (by omega) hl
  rw [ge_iff_le, condProb, ENNReal.le_div_iff_mul_le (.inl hpos) (.inl (ne_top_of_le_ne_top one_ne_top (prob_le_one _ _)))]
  exact Sure.genTypeEnvB_instance_varied_length b s l hb

end Cedar.Validation.Relational.Claims
