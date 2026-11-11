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

import CedarGen.Relational.SchemaGenFComplete
import CedarGen.Relational.SchemaGenFDerive
import Specimen.Correctness.Workers

/-! # What the flagged schema generator describes, exactly

* `genTypeEnvF_iff_envAssumptions`: with every flag `false`, exactly the environments satisfying
  `EnvAssumptions` (the hypothesis of `hasType_iff_typeOf_ok`) within the budget;
* `genTypeEnvF_iff_typeEnvWF`, `genTypeEnvF_iff_validateWellFormed`: with the four `wf` flags,
  exactly the well-formed environments within the budget;
* `GenTypeEnvF.envAssumptions` (soundness at every setting), `GenTypeEnvF.typeEnvWF` (with the `wf`
  flags, whatever the others) and `GenTypeEnvF.mono` (monotone in each flag);
* the same of the derived generator, at the level of what it produces: `genTypeEnvF_generated`,
  `genTypeEnvF_instance_complete_*`. -/

namespace Cedar.Validation.Relational.SchemaGen

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Specimen.Correctness Basalt

/-- **`typeOf`'s hypothesis, exactly.** With every flag `false`, `GenTypeEnvF` (in some mode)
describes exactly the environments satisfying `EnvAssumptions` with at most `budget` request
environments. -/
theorem genTypeEnvF_iff_envAssumptions {b : Nat} {env : TypeEnv} :
    (∃ r, GenTypeEnvF false false false false false false false r b env) ↔
      EnvAssumptions env ∧ env.schema.environments.length ≤ b :=
  ⟨fun ⟨_, h⟩ => h.envAssumptions,
   fun ⟨h, hb⟩ => ⟨.dense, GenTypeEnvF.complete_envAssumptions h hb⟩⟩

/-- **`validateWellFormed`'s environments, exactly.** With `wfMaps`, `wfActs`, `wfEnum` and
`wfRest`, `GenTypeEnvF` (in some mode) describes exactly the `TypeEnvWF` environments with at
most `budget` request environments. -/
theorem genTypeEnvF_iff_typeEnvWF {b : Nat} {env : TypeEnv} :
    (∃ r, GenTypeEnvF true true true true false false false r b env) ↔
      TypeEnvWF env ∧ env.schema.environments.length ≤ b :=
  ⟨fun ⟨_, h⟩ => ⟨h.typeEnvWF, h.envAssumptions.2⟩,
   fun ⟨h, hb⟩ => ⟨.dense, GenTypeEnvF.complete_typeEnvWF h hb⟩⟩

theorem genTypeEnvF_iff_validateWellFormed {b : Nat} {env : TypeEnv} :
    (∃ r, GenTypeEnvF true true true true false false false r b env) ↔
      env.validateWellFormed = .ok () ∧ env.schema.environments.length ≤ b := by
  rw [genTypeEnvF_iff_typeEnvWF, typeEnvWF_iff_validateWellFormed]

/-- The DRT setting (every flag `true`) is well-formed. -/
theorem GenTypeEnvF.validateWellFormed_all {r b env}
    (h : GenTypeEnvF true true true true true true true r b env) :
    env.validateWellFormed = .ok () :=
  typeEnvWF_iff_validateWellFormed.mp h.typeEnvWF

/-! ## The Rust-shape flags -/

theorem CloseEnts.closed {m g g'} (h : CloseEnts true m g g') : closedB entAncs g' = true := by
  cases h with
  | closeS => assumption
  | closeA => assumption

/-- With `closed`, the entity hierarchy is transitively closed. -/
theorem GenTypeEnvF.closed {m a e d n i r b env} (h : GenTypeEnvF m a e d true n i r b env) :
    closedB entAncs env.ets.toList = true := by
  match h with
  | .decl _ _ _ _ _ _ _ _ _ _ _ _ _ _ hents _ => cases hents; case mk h => exact h.closed
  | .free _ _ _ _ _ _ _ _ _ _ _ _ _ _ hents _ _ => cases hents; case mk h => exact h.closed

/-- With `idents`, every entity type name is an identifier path and every action type
`ns::Action`, and no name shadows one in the empty namespace, as Rust's schemas have them. -/
theorem GenTypeEnvF.idents {m a e d c n r b env} (h : GenTypeEnvF m a e d c n true r b env) :
    (∀ p ∈ env.ets.toList, isIdentName p.1 = true) ∧
      (∀ p ∈ env.acts.toList, isActionType p.1.ty = true) ∧
      noShadowB (env.ets.toList.map Prod.fst) (env.acts.toList.map Prod.fst) = true := by
  have key : ∀ {sk : Skeleton} {ents : List (EntityType × EntitySchemaEntry)}
      {acts : List (EntityUID × ActionSchemaEntry)}, SkelInv m a true sk → ents.map Prod.fst = sk.ks →
      acts.map Prod.fst = sk.uids →
      (∀ p ∈ ents, isIdentName p.1 = true) ∧ (∀ p ∈ acts, isActionType p.1.ty = true) ∧
        noShadowB (ents.map Prod.fst) (acts.map Prod.fst) = true := by
    intro sk ents acts hinv he ha
    refine ⟨?_, ?_, by rw [he, ha]; exact hinv.no_shadow rfl⟩
    · intro p hp
      have : p.1 ∈ sk.ks := by rw [← he]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
      cases hinv.ks_names _ this with
      | ident => assumption
    · intro p hp
      have : p.1 ∈ sk.uids := by rw [← ha]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
      cases hinv.uids_ty _ this
      case mk h _ => cases h with | action => assumption
  match h with
  | .decl _ _ _ _ _ _ _ _ _ _ _ _ _ hsk hents hacts =>
    have hinv := hsk.inv
    exact key hinv (hents.ok hinv).1 (hacts.ok hinv).1
  | .free _ _ _ _ _ _ _ _ _ _ _ _ _ hsk hents hacts _ =>
    have hinv := hsk.inv
    exact key hinv (hents.ok hinv).1 (hacts.ok hinv).1

/-! ## The derived generator -/

/-- The derived worker for `fun m a e d c n i budget => ∃ r env, GenTypeEnvF …`. -/
noncomputable abbrev genTypeEnvFWorker := worker% gen SchemaGen.GenTypeEnvF [7, 9] (G := SGen)

/-- **Sound.** Every environment the derived generator produces, at any fuel, size and leaf size and
any flags, is in `GenTypeEnvF`; hence it satisfies `EnvAssumptions` within the budget. -/
theorem genTypeEnvF_generated (fuel iS sz : Nat) (m a e d c n i : Bool) (b : Nat) (r : HierMode)
    (env : TypeEnv)
    (h : Produces (genTypeEnvFWorker fuel iS sz m a e d c n i b : SGen _) (r, env)) :
    GenTypeEnvF m a e d c n i r b env :=
  (worker% gen SchemaGen.GenTypeEnvF [7, 9] sound) fuel iS sz m a e d c n i b (r, env) h

theorem genTypeEnvF_instance_generated (m a e d c n i : Bool) (b s l : Nat) (r : HierMode)
    (env : TypeEnv)
    (h : Produces (BacktrackGenFor.gen
      (P := fun p : HierMode × TypeEnv => GenTypeEnvF m a e d c n i p.1 b p.2) (G := SGen) s l)
      (r, env)) :
    GenTypeEnvF m a e d c n i r b env :=
  genTypeEnvF_generated _ _ _ m a e d c n i b r env h

/-- …satisfying `EnvAssumptions` within the budget at every setting… -/
theorem genTypeEnvF_instance_envAssumptions (m a e d c n i : Bool) (b s l : Nat) (r : HierMode)
    (env : TypeEnv)
    (h : Produces (BacktrackGenFor.gen
      (P := fun p : HierMode × TypeEnv => GenTypeEnvF m a e d c n i p.1 b p.2) (G := SGen) s l)
      (r, env)) :
    EnvAssumptions env ∧ env.schema.environments.length ≤ b :=
  (genTypeEnvF_instance_generated m a e d c n i b s l r env h).envAssumptions

/-- …and well-formed with the `wf` flags (in particular in the DRT setting, every flag `true`). -/
theorem genTypeEnvF_instance_validateWellFormed (c n i : Bool) (b s l : Nat) (r : HierMode)
    (env : TypeEnv)
    (h : Produces (BacktrackGenFor.gen
      (P := fun p : HierMode × TypeEnv => GenTypeEnvF true true true true c n i p.1 b p.2)
      (G := SGen) s l) (r, env)) :
    env.validateWellFormed = .ok () ∧ env.schema.environments.length ≤ b :=
  have h := genTypeEnvF_instance_generated _ _ _ _ c n i b s l r env h
  ⟨typeEnvWF_iff_validateWellFormed.mp h.typeEnvWF, h.envAssumptions.2⟩

/-- **Complete.** At any flags, every environment of `GenTypeEnvF` is generated, in its mode, at
every large enough size and leaf size. -/
theorem genTypeEnvF_instance_complete (m a e d c n i : Bool) (b : Nat) (r : HierMode)
    (env : TypeEnv) (h : GenTypeEnvF m a e d c n i r b env) :
    ∃ k, ∀ s l, k ≤ s → k ≤ l →
      Produces (BacktrackGenFor.gen
        (P := fun p : HierMode × TypeEnv => GenTypeEnvF m a e d c n i p.1 b p.2) (G := SGen) s l)
        (r, env) :=
  BacktrackGenForComplete.complete (r, env) h

/-- With every flag `false`, every `EnvAssumptions` environment within the budget is generated. -/
theorem genTypeEnvF_instance_complete_envAssumptions (b : Nat) (env : TypeEnv)
    (h : EnvAssumptions env) (hb : env.schema.environments.length ≤ b) :
    ∃ r k, ∀ s l, k ≤ s → k ≤ l →
      Produces (BacktrackGenFor.gen
        (P := fun p : HierMode × TypeEnv =>
          GenTypeEnvF false false false false false false false p.1 b p.2) (G := SGen) s l) (r, env) :=
  ⟨.dense, genTypeEnvF_instance_complete _ _ _ _ _ _ _ b _ env (GenTypeEnvF.complete_envAssumptions h hb)⟩

/-- With the four `wf` flags, every well-formed environment within the budget is generated. -/
theorem genTypeEnvF_instance_complete_typeEnvWF (b : Nat) (env : TypeEnv)
    (h : TypeEnvWF env) (hb : env.schema.environments.length ≤ b) :
    ∃ r k, ∀ s l, k ≤ s → k ≤ l →
      Produces (BacktrackGenFor.gen
        (P := fun p : HierMode × TypeEnv =>
          GenTypeEnvF true true true true false false false p.1 b p.2) (G := SGen) s l) (r, env) :=
  ⟨.dense, genTypeEnvF_instance_complete _ _ _ _ _ _ _ b _ env (GenTypeEnvF.complete_typeEnvWF h hb)⟩

end Cedar.Validation.Relational.SchemaGen

#print axioms Cedar.Validation.Relational.SchemaGen.genTypeEnvF_iff_envAssumptions
#print axioms Cedar.Validation.Relational.SchemaGen.genTypeEnvF_iff_typeEnvWF
#print axioms Cedar.Validation.Relational.SchemaGen.genTypeEnvF_iff_validateWellFormed
#print axioms Cedar.Validation.Relational.SchemaGen.GenTypeEnvF.mono
#print axioms Cedar.Validation.Relational.SchemaGen.GenTypeEnvF.envAssumptions
#print axioms Cedar.Validation.Relational.SchemaGen.GenTypeEnvF.typeEnvWF
#print axioms Cedar.Validation.Relational.SchemaGen.GenTypeEnvF.validateWellFormed_all
#print axioms Cedar.Validation.Relational.SchemaGen.GenTypeEnvF.closed
#print axioms Cedar.Validation.Relational.SchemaGen.GenTypeEnvF.idents
#print axioms Cedar.Validation.Relational.SchemaGen.genTypeEnvF_generated
#print axioms Cedar.Validation.Relational.SchemaGen.genTypeEnvF_instance_envAssumptions
#print axioms Cedar.Validation.Relational.SchemaGen.genTypeEnvF_instance_validateWellFormed
#print axioms Cedar.Validation.Relational.SchemaGen.genTypeEnvF_instance_complete
#print axioms Cedar.Validation.Relational.SchemaGen.genTypeEnvF_instance_complete_envAssumptions
#print axioms Cedar.Validation.Relational.SchemaGen.genTypeEnvF_instance_complete_typeEnvWF
