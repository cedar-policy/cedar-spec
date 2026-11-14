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

import CedarGen.Relational.Sound.SchemaSure
import CedarGen.Relational.Sound.SparseAncestors
import Specimen.Correctness.Workers

/-! # The schema generator's distribution, as its instance runs it

* `genTypeEnvB_instance_varied(_length)`: with a budget of at least two, a schema with at least two
  entity types has two distinct request environments with probability at least `5/18`;
* `genTypeEnvB_instance_sparse_mean(_log)`: in the sparse mode, the mean number of ancestors of a
  standard entity type is at most `H(l + 1) - 1 ≤ ln (l + 1)`, `l` the leaf size.

Both are over the generator's successes, and it never fails (`genTypeEnvB_instance_sok`). -/

namespace Cedar.Validation.Relational.SchemaGen.Sure

open Cedar.Spec Cedar.Validation Cedar.Validation.Relational Cedar.Validation.Relational.Schema
open Specimen.Correctness Specimen.Backtrack Basalt ENNReal Sound

variable {A B : Type}

/-! ## Combinations -/

/-- The (principal, action, resource) combinations the actions declare: a schema's request
environments, up to the context, which is the action's. -/
def combos (acts : List (EntityUID × ActionSchemaEntry)) : List (EntityType × EntityUID × EntityType) :=
  acts.flatMap fun x => (x.2.appliesToPrincipal.toList.product x.2.appliesToResource.toList).map
    fun pr => (pr.1, x.1, pr.2)

/-- At least two distinct combinations. -/
def Varied (acts : List (EntityUID × ActionSchemaEntry)) : Prop :=
  ∃ x ∈ combos acts, ∃ y ∈ combos acts, x ≠ y

theorem mem_product {α β : Type} {l₁ : List α} {l₂ : List β} {a : α} {b : β} (ha : a ∈ l₁) (hb : b ∈ l₂) :
    (a, b) ∈ l₁.product l₂ := by
  simp only [List.product, List.mem_flatMap, List.mem_map]
  exact ⟨a, ha, b, hb, rfl⟩

theorem mem_combos_head {a : EntityUID} {e : ActionSchemaEntry} {acts} {p r : EntityType}
    (hp : p ∈ e.appliesToPrincipal.toList) (hr : r ∈ e.appliesToResource.toList) :
    (p, a, r) ∈ combos ((a, e) :: acts) := by
  simp only [combos, List.flatMap_cons, List.mem_append, List.mem_map]
  exact .inl ⟨(p, r), mem_product hp hr, rfl⟩

theorem mem_combos_tail {x : EntityUID × ActionSchemaEntry} {acts} {c} (h : c ∈ combos acts) :
    c ∈ combos (x :: acts) := by
  simp only [combos, List.flatMap_cons, List.mem_append] at h ⊢
  exact .inr h

theorem combos_action {acts : List (EntityUID × ActionSchemaEntry)} {c} (h : c ∈ combos acts) :
    ∃ x ∈ acts, c.2.1 = x.1 := by
  simp only [combos, List.mem_flatMap, List.mem_map] at h
  obtain ⟨x, hx, pr, -, rfl⟩ := h
  exact ⟨x, hx, rfl⟩

theorem varied_cons {x : EntityUID × ActionSchemaEntry} {acts} (h : Varied acts) : Varied (x :: acts) := by
  obtain ⟨c, hc, d, hd, hne⟩ := h
  exact ⟨c, mem_combos_tail hc, d, mem_combos_tail hd, hne⟩

theorem requestFromAction_combos {ets acts reqty} (h : RequestFromAction ets acts reqty) :
    (reqty.principal, reqty.action, reqty.resource) ∈ combos acts := by
  induction h with
  | here _ _ _ _ _ _ _ _ hp hr => exact mem_combos_head (mem_of_definedEntityType hp) (mem_of_definedEntityType hr)
  | there _ _ _ _ ih => exact mem_combos_tail ih

theorem selectRemove_facts {α : Type} {xs : List α} {y : α} {ys : List α} (h : SelectRemove xs y ys) :
    y ∈ xs ∧ (∀ z ∈ ys, z ∈ xs) ∧ (xs.Nodup → y ∉ ys ∧ ys.Nodup) := by
  induction h with
  | here x xs => exact ⟨List.mem_cons_self, fun z hz => List.mem_cons_of_mem _ hz,
      fun hd => ⟨(List.nodup_cons.mp hd).1, (List.nodup_cons.mp hd).2⟩⟩
  | there x xs y ys _ ih =>
    refine ⟨List.mem_cons_of_mem _ ih.1, fun z hz => ?_, fun hd => ?_⟩
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih.2.1 z hz)
    · obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hd
      obtain ⟨hy, hys⟩ := ih.2.2 hxs
      refine ⟨fun hm => ?_, List.nodup_cons.mpr ⟨fun hx' => hx (ih.2.1 x hx'), hys⟩⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hx ih.1
      · exact hy hm

theorem wfActionsGo_eids {ets built avail acts} (h : WfActionsGo ets built avail acts) :
    ∀ x ∈ acts, x.1.eid ∈ avail := by
  induction h with
  | nil => simp
  | cons _ _ _ _ _ _ _ _ _ hsel _ _ _ _ _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (selectRemove_facts hsel).1
    · exact (selectRemove_facts hsel).2.1 _ (ih x hx)

/-- The request's action is among the actions, its name from the pool. -/
theorem wfActionsGoR_request {r ets built avail b acts reqty} (h : WfActionsGoR r ets built avail b acts reqty) :
    (reqty.principal, reqty.action, reqty.resource) ∈ combos acts ∧ reqty.action.eid ∈ avail := by
  have hw := h.wfActionsGo
  have hc := requestFromAction_combos hw.2
  obtain ⟨x, hx, hxa⟩ := combos_action hc
  have : reqty.action = x.1 := hxa
  exact ⟨hc, this ▸ wfActionsGo_eids hw.1 x hx⟩

theorem five_eighteenths (n : ℕ) (hn : 2 ≤ n) :
    (5 : ℝ≥0∞) / 18 ≤ 5 * ((((n - 1 : ℕ) : ℝ≥0∞) * 1) / (n : ℝ≥0∞)) / 9 := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hhalf : (1 : ℝ≥0∞) / 2 ≤ ((n - 1 : ℕ) : ℝ≥0∞) * 1 / n := by
    rw [mul_one, ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n))]
    have h2 : (n : ℝ≥0∞) ≤ 2 * ((n - 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast (show n ≤ 2 * (n - 1) by omega)
    calc 1 / 2 * (n : ℝ≥0∞) ≤ 1 / 2 * (2 * ((n - 1 : ℕ) : ℝ≥0∞)) := by gcongr
      _ = ((n - 1 : ℕ) : ℝ≥0∞) := by
        rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  calc (5 : ℝ≥0∞) / 18 = 5 * (1 / 2) / 9 := by
        have h : (18 : ℝ≥0∞) = 2 * 9 := by norm_num
        rw [h, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (by simp) (by simp), mul_one_div,
          div_eq_mul_inv, mul_assoc]
    _ ≤ _ := by gcongr

/-- Whether the actions declare two combinations. -/
noncomputable def evVar : (List (EntityUID × ActionSchemaEntry) × RequestType) → ℝ≥0∞ :=
  Set.indicator {o | Varied o.1} 1

theorem one_le_evVar {o : List (EntityUID × ActionSchemaEntry) × RequestType} (h : Varied o.1) :
    1 ≤ evVar o := by
  simp [evVar, Set.indicator, h]

/-- An action with two distinct principals declares two combinations. -/
theorem varied_of_two_principals {uid : EntityUID} {ps rs : List EntityType} {anc ctx}
    {rest : List (EntityUID × ActionSchemaEntry)} {p z r : EntityType} (hp : p ∈ ps) (hz : z ∈ ps)
    (hzp : z ≠ p) (hr : r ∈ rs) :
    Varied ((uid, ActionSchemaEntry.mk (Cedar.Data.Set.mk ps) (Cedar.Data.Set.mk rs) anc ctx) :: rest) :=
  ⟨_, mem_combos_head hp hr, _, mem_combos_head hz hr, fun h => hzp (congrArg Prod.fst h).symm⟩

/-- An action placed before the request's, with a name the rest cannot draw, that declares a
combination: that combination and the request's differ in their action. -/
theorem varied_of_earlier {r ets built avail b rest reqty} {ty : EntityType} {eid : String}
    {ps rs : List EntityType} {anc ctx} {p r₀ : EntityType} (hrest : WfActionsGoR r ets built avail b rest reqty)
    (heid : eid ∉ avail) (hp : p ∈ ps) (hr : r₀ ∈ rs) :
    Varied ((⟨ty, eid⟩, ActionSchemaEntry.mk (Cedar.Data.Set.mk ps) (Cedar.Data.Set.mk rs) anc ctx) :: rest) := by
  have hw := wfActionsGoR_request hrest
  refine ⟨_, mem_combos_head hp hr, _, mem_combos_tail hw.1, fun h => heid ?_⟩
  have : (⟨ty, eid⟩ : EntityUID) = reqty.action := congrArg (fun x => x.2.1) h
  rw [show eid = reqty.action.eid from congrArg EntityUID.eid this]
  exact hw.2

theorem _root_.Cedar.Validation.Relational.SchemaGen.ContainsBounded.mem {ets n x xs} (h : ContainsBounded ets n x xs) : x ∈ xs := by
  induction h with
  | here => exact List.mem_cons_self
  | there _ _ _ _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem evVar_cons_le (x : EntityUID × ActionSchemaEntry) (o : List (EntityUID × ActionSchemaEntry) × RequestType) :
    evVar o ≤ evVar (x :: o.1, o.2) := by
  by_cases hv : Varied o.1
  · exact (by simp [evVar, Set.indicator, hv] : evVar o ≤ 1).trans (one_le_evVar (varied_cons hv))
  · simp [evVar, Set.indicator, hv]

/-- **The actions are varied.** With at least two distinct entity types, a budget of at least two
environments, distinct names to draw from and a leaf size of at least one, the actions, over their
successes, declare two distinct combinations with probability at least `5/18`: the request's action,
drawn first, has a second principal with probability at least `5/9 · (1 - 1/n) ≥ 5/18`; an action
drawn before it either declares a combination of its own, distinct from the request's by its name,
or leaves the budget whole. -/
theorem wa_varied (iS : Nat) (hiS : 1 ≤ iS) (r : HierMode) (ets : List EntityType) (hd : ets.Nodup)
    (hn : 2 ≤ ets.length) : ∀ (fuel sz : Nat) (built : List (EntityUID × List EntityUID))
    (avail : List String) (b : Nat), avail.Nodup → 2 ≤ b →
    MeanLeW (actionsGen fuel iS sz r ets built avail b) (fun _ => 5 / 18) evVar 1
  | 0, _, _, _, _, _, _ => by
    rw [actionsGen, (worker% gen SchemaGen.WfActionsGoR [5, 6] eq_def)]
    exact meanLeW_of_zero (sexpect_outOfFuel _)
  | f + 1, sz, built, avail, b, hav, hb => by
    have hne : ets ≠ [] := List.ne_nil_of_length_pos (by omega)
    rw [actionsGen, (worker% gen SchemaGen.WfActionsGoR [5, 6] eq_def)]
    rcases sz with _ | s <;> refine meanLeW_backtrack ?_ <;>
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] <;>
      apply And.intro
    -- the request's action, drawn here: a second principal with probability `≥ 5/18`
    case left | left =>
      refine meanLeW_bind_const fun _ => meanLeW_bind_const fun _ => meanLeW_bind_const fun _ => ?_
      apply meanLeW_bind_event (V := {x | ∃ z ∈ x.2, z ≠ x.1}) (Variety.cb_sok iS (iS + 1) iS ets b hne (by omega) (by omega))
        ((five_eighteenths _ hn).trans (Variety.cb_variety iS (iS + 1) iS ets b hd hne hb hiS (by omega)))
      case hq =>
        rintro ⟨p, ps⟩ hp
        have hcb := (worker% gen SchemaGen.ContainsBounded [2, 3] sound) (iS + 1) iS iS ets b (p, ps) hp
        have hpos : 0 < ps.length := List.length_pos_iff.mpr hcb.definedEntityType.ne_nil
        exact sok_bind_sure (Variety.cb_sok iS (iS + 1) iS ets (b / ps.length) hne
            (Nat.div_pos hcb.boundedTypes.length_le hpos) (by omega)) fun ⟨_, _⟩ =>
          sok_bind_eq fun ⟨_, _⟩ => (sok_bind_eq fun _ => sok_bind_one (sok_wb _ _ _ _ _ _ _ _) fun _ => sok_pure _).trans
            (mul_one _)
      case hk =>
        rintro ⟨p, ps⟩ hp ⟨z, hz, hzp⟩ o ho
        simp only [produces_bind_iff, produces_pure_iff, Prod.exists] at ho
        obtain ⟨res, rs, hres, -, -, -, -, -, -, -, rfl⟩ := ho
        have hcb := (worker% gen SchemaGen.ContainsBounded [2, 3] sound) (iS + 1) iS iS ets b (p, ps) hp
        have hcr := (worker% gen SchemaGen.ContainsBounded [2, 3] sound) (iS + 1) iS iS ets _ (res, rs) hres
        exact one_le_evVar (varied_of_two_principals hcb.mem hz hzp hcr.mem)
    case right => exact meanLeW_truncations
    -- an action before the request's: no environments, and the request's chance is kept; or some, and
    -- the actions are varied surely
    case right =>
      refine meanLeW_bind_const fun _ => meanLeW_bind_const fun ps => meanLeW_bind_const fun _ =>
        meanLeW_bind_const fun rs => meanLeW_bind_support fun ⟨eid, av'⟩ hz => meanLeW_bind_const fun _ => ?_
      have hsel := (worker% gen Schema.SelectRemove [2, 3] sound) (iS + 1) iS iS String avail (eid, av') hz
      obtain ⟨heid, hav'⟩ := (selectRemove_facts hsel).2.2 hav
      by_cases h0 : ps.length * rs.length = 0
      · refine meanLeW_tail (q := 1) (wa_varied iS hiS r ets hd hn f s _ av' _ hav' (by rw [h0]; omega))
          (fun _ => by simp [sexpect_pure]) (fun o => by simpa [sexpect_pure] using evVar_cons_le _ o) le_rfl
      · refine meanLeW_const_of_all (ENNReal.div_le_of_le_mul (by norm_num)) fun o ho => ?_
        simp only [produces_bind_iff, produces_pure_iff, Prod.exists] at ho
        obtain ⟨rest, g5, hrest, rfl⟩ := ho
        obtain ⟨p₀, hp₀⟩ := List.exists_mem_of_ne_nil ps (by rintro rfl; simp at h0)
        obtain ⟨r₀, hr₀⟩ := List.exists_mem_of_ne_nil rs (by rintro rfl; simp at h0)
        exact one_le_evVar (varied_of_earlier
          ((worker% gen SchemaGen.WfActionsGoR [5, 6] sound) _ _ _ _ _ _ _ _ (rest, g5) hrest) heid hp₀ hr₀)


/-! ## The whole generator -/

theorem notInET_not_mem {et : EntityType} {names : List EntityType} (h : NotInET et names) : et ∉ names := by
  induction h with
  | nil => simp
  | cons _ _ hne _ ih => simp only [List.mem_cons, not_or]; exact ⟨hne, ih⟩

theorem wfEntitiesGoR_names {r built names allNames rest} (h : WfEntitiesGoR r built names allNames rest) :
    names.Nodup → allNames.Nodup ∧ allNames.length = names.length + rest.length := by
  induction h with
  | nil => intro hd; exact ⟨hd, by simp⟩
  | standard _ _ _ _ _ _ _ _ hnot _ _ _ _ ih =>
    intro hd
    obtain ⟨h1, h2⟩ := ih (List.nodup_cons.mpr ⟨notInET_not_mem hnot, hd⟩)
    exact ⟨h1, by simp only [List.length_cons] at h2 ⊢; omega⟩
  | enum _ _ _ _ _ _ hnot _ ih =>
    intro hd
    obtain ⟨h1, h2⟩ := ih (List.nodup_cons.mpr ⟨notInET_not_mem hnot, hd⟩)
    exact ⟨h1, by simp only [List.length_cons] at h2 ⊢; omega⟩

/-- The entity schema's names are distinct, one per entry. -/
theorem wfEntitiesGo1_names {r names entries} (h : WfEntitiesGo1 r [] [] names entries) :
    names.Nodup ∧ names.length = entries.length := by
  cases h with
  | standard _ _ _ _ _ _ _ _ _ _ h | enum _ _ _ _ _ h =>
    obtain ⟨h1, h2⟩ := wfEntitiesGoR_names h (List.nodup_singleton _)
    exact ⟨h1, by simp only [List.length_cons, List.length_nil] at h2 ⊢; omega⟩

/-- A combination is a request environment's. -/
theorem mem_environments {ets : EntitySchema} {acts : List (EntityUID × ActionSchemaEntry)} {reqty : RequestType}
    {c : EntityType × EntityUID × EntityType} (h : c ∈ combos acts) :
    ∃ e ∈ (TypeEnv.mk ets (Cedar.Data.Map.mk acts) reqty).schema.environments,
      (e.reqty.principal, e.reqty.action, e.reqty.resource) = c := by
  simp only [combos, List.mem_flatMap, List.mem_map] at h
  obtain ⟨⟨a, e⟩, hae, ⟨p, r⟩, hpr, rfl⟩ := h
  refine ⟨⟨ets, Cedar.Data.Map.mk acts, ⟨p, a, r, e.context⟩⟩, ?_, rfl⟩
  show _ ∈ List.map _ (List.flatMap _ acts)
  refine List.mem_map.mpr ⟨⟨p, a, r, e.context⟩, List.mem_flatMap.mpr ⟨(a, e), hae, ?_⟩, rfl⟩
  show _ ∈ List.map _ (List.product _ _)
  exact List.mem_map.mpr ⟨(p, r), hpr, rfl⟩

/-- Two distinct combinations, two distinct request environments. -/
theorem varied_environments {ets : EntitySchema} {acts : List (EntityUID × ActionSchemaEntry)} {reqty : RequestType}
    (h : Varied acts) :
    ∃ e₁ ∈ (TypeEnv.mk ets (Cedar.Data.Map.mk acts) reqty).schema.environments,
      ∃ e₂ ∈ (TypeEnv.mk ets (Cedar.Data.Map.mk acts) reqty).schema.environments, e₁ ≠ e₂ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  obtain ⟨e₁, h₁, rfl⟩ := mem_environments (ets := ets) (reqty := reqty) hx
  obtain ⟨e₂, h₂, rfl⟩ := mem_environments (ets := ets) (reqty := reqty) hy
  exact ⟨e₁, h₁, e₂, h₂, fun h => hxy (h ▸ rfl)⟩

/-- At leaf size `0` the entity schema declares one type. -/
theorem we_size0 {f iS : Nat} {r : HierMode} {b : List (EntityType × List EntityType)} {names : List EntityType}
    {out : List EntityType × List (EntityType × EntitySchemaEntry)} (h : Produces (entitiesGen (f + 1) iS 0 r b names) out) :
    out.2 = [] := by
  rw [entitiesGen, (worker% gen SchemaGen.WfEntitiesGoR [3, 4] eq_def)] at h
  simp only [produces_backtrack_iff, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp,
    exists_eq_left, produces_truncations_iff] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · simp only [produces_pure_iff] at h; rw [h]
  · exact h.elim

theorem we0_size0 {f iS : Nat} {b : List (EntityType × List EntityType)} {names : List EntityType}
    {out : HierMode × List EntityType × List (EntityType × EntitySchemaEntry)} (h : Produces (entitiesModeGen (f + 1) iS 0 b names) out) :
    out.2.2 = [] := by
  rw [entitiesModeGen, (worker% gen SchemaGen.WfEntitiesGoR [0, 3, 4] eq_def)] at h
  simp only [produces_backtrack_iff, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp,
    exists_eq_left, produces_truncations_iff] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · simp only [produces_bind_iff, produces_pure_iff] at h
    obtain ⟨_, -, rfl⟩ := h; rfl
  · exact h.elim

theorem we1_size0 {f : Nat} {out : HierMode × List EntityType × List (EntityType × EntitySchemaEntry)}
    (h : Produces (entities1Gen (f + 1) 0 0 [] []) out) : out.2.2.length = 1 := by
  rw [entities1Gen, (worker% gen SchemaGen.WfEntitiesGo1 [0, 3, 4] eq_def)] at h
  simp only [produces_backtrack_iff, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp,
    exists_eq_left] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · simp only [produces_bind_iff, produces_pure_iff, Prod.exists] at h
    obtain ⟨_, -, _, -, _, -, _, _, -, _, _, hwe, rfl⟩ := h
    have h0 := we_size0 (f := 0) (iS := 0) hwe
    simp only at h0
    simp [h0]
  · simp only [produces_bind_iff, produces_pure_iff, Prod.exists] at h
    obtain ⟨_, -, _, _, _, hwe, _, -, rfl⟩ := h
    have h0 := we0_size0 (f := 0) (iS := 0) hwe
    simp only at h0
    simp [h0]


theorem single_branch_le {b : Unit → SGen A} {E F : Set A} {c : ℝ≥0∞} (hb : sok (b ()) = 1)
    (h : c * sprob (b ()) E ≤ sprob (b ()) F) :
    c * sprob (Specimen.Backtrack.backtrack [(1, b)]) E ≤ sprob (Specimen.Backtrack.backtrack [(1, b)]) F := by
  unfold sprob at *
  rw [sexpect_backtrack_eq _ _ (by simp [sumWeights]) (by simpa using hb),
    sexpect_backtrack_eq _ _ (by simp [sumWeights]) (by simpa using hb)]
  simpa [sumWeights] using h

theorem actionEidPool_nodup : actionEidPool.Nodup := by decide

/-- **Schemas are varied.** As its instance runs it, with a budget of at least two
request environments, the schema generator (which never fails, `genTypeEnvB_instance_sok`) produces
a schema with two distinct request environments, given that it has at least two entity types, with
probability at least `5/18`. -/
theorem genTypeEnvB_instance_varied (budget s l : Nat) (hb : 2 ≤ budget) :
    5 / 18 * sprob (BacktrackGenFor.gen (P := fun p : HierMode × TypeEnv => GenTypeEnvB p.1 budget p.2)
        (G := SGen) s l) {p | 2 ≤ p.2.ets.toList.length} ≤
      sprob (BacktrackGenFor.gen (P := fun p : HierMode × TypeEnv => GenTypeEnvB p.1 budget p.2)
        (G := SGen) s l)
        {p | 2 ≤ p.2.ets.toList.length ∧
          ∃ e₁ ∈ p.2.schema.environments, ∃ e₂ ∈ p.2.schema.environments, e₁ ≠ e₂} := by
  show 5 / 18 * sprob (typeEnvGen (s + 1) l s budget) _ ≤ sprob (typeEnvGen (s + 1) l s budget) _
  rw [typeEnvGen, (worker% gen SchemaGen.GenTypeEnvB [0, 2] eq_def)]
  rcases s with _ | s <;> apply single_branch_le
  case hb | hb =>
    refine sok_bind_one_of_support (sok_we1 l l l) fun ⟨r, names, entries⟩ => fun hp => ?_
    have hne := wfEntitiesGo1_names_ne_nil
      ((worker% gen SchemaGen.WfEntitiesGo1 [0, 3, 4] sound)
        (l + 1) l l [] [] _ hp)
    exact sok_bind_one (sok_wa_top l l l r names actionEidPool budget hne
      (by simp [actionEidPool]) (by omega)) fun _ => sok_pure _
  case h | h =>
    unfold sprob
    rw [sexpect_bind, sexpect_bind, ← sexpect_mul_left]
    refine sexpect_mono_support fun o ho => ?_
    obtain ⟨r, names, entries⟩ := o
    have hw := (worker% gen SchemaGen.WfEntitiesGo1 [0, 3, 4] sound)
      (l + 1) l l [] [] _ ho
    obtain ⟨hnd, hlen⟩ := wfEntitiesGo1_names hw
    dsimp only
    rw [sexpect_bind, sexpect_bind]
    by_cases h2 : 2 ≤ entries.length
    · have hl : 1 ≤ l := by
        rcases Nat.eq_zero_or_pos l with rfl | h
        · have := we1_size0 (f := 0) ho; simp only at this; omega
        · exact h
      have hva := wa_varied l hl r names hnd (hlen ▸ h2) (l + 1) l [] actionEidPool budget
        actionEidPool_nodup hb
      unfold MeanLeW at hva
      rw [sexpect_const', one_mul, mul_comm] at hva
      calc _ = 5 / 18 * sok (actionsGen (l + 1) l l r names [] actionEidPool budget) := by
             congr 1; unfold sok
             exact sexpect_congr _ fun x => by
               obtain ⟨acts, reqty⟩ := x
               simp [sexpect_pure, Set.indicator, Cedar.Data.Map.toList, h2]
        _ ≤ sexpect (actionsGen (l + 1) l l r names [] actionEidPool budget) evVar := hva
        _ ≤ _ := sexpect_mono _ fun x => by
             obtain ⟨acts, reqty⟩ := x
             rw [sexpect_pure]
             by_cases hv : Varied acts
             · refine (by simp [evVar, Set.indicator, hv] : evVar (acts, reqty) ≤ 1).trans (le_of_eq ?_)
               have := varied_environments (ets := Cedar.Data.Map.mk entries) (reqty := reqty) hv
               exact (Set.indicator_of_mem (show _ ∈ {p : HierMode × TypeEnv | 2 ≤ p.2.ets.toList.length ∧
                 ∃ e₁ ∈ p.2.schema.environments, ∃ e₂ ∈ p.2.schema.environments, e₁ ≠ e₂} from
                 ⟨by simpa [Cedar.Data.Map.toList] using h2, this⟩) 1).symm
             · simp [evVar, Set.indicator, hv]
    · refine le_of_eq_of_le ?_ zero_le
      rw [mul_eq_zero]; right
      refine (sexpect_congr _ fun x => ?_).trans (sexpect_zero_fun _)
      obtain ⟨acts, reqty⟩ := x
      simp [sexpect_pure, Set.indicator, Cedar.Data.Map.toList, h2]

theorem two_le_length_of_ne {α : Type} {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    2 ≤ l.length := by
  match l, ha, hb with
  | [], ha, _ => simp at ha
  | [x], ha, hb => exact absurd ((List.mem_singleton.mp ha).trans (List.mem_singleton.mp hb).symm) hne
  | _ :: _ :: _, _, _ => simp

theorem sexpect_congr_support {g : SGen A} {f f' : A → ℝ≥0∞} (h : ∀ a, Produces g a → f a = f' a) :
    sexpect g f = sexpect g f' :=
  le_antisymm (sexpect_mono_support fun a ha => (h a ha).le) (sexpect_mono_support fun a ha => (h a ha).ge)

/-- Two distinct request environments: at least two. -/
theorem genTypeEnvB_instance_varied_length (budget s l : Nat) (hb : 2 ≤ budget) :
    5 / 18 * sprob (BacktrackGenFor.gen (P := fun p : HierMode × TypeEnv => GenTypeEnvB p.1 budget p.2)
        (G := SGen) s l) {p | 2 ≤ p.2.ets.toList.length} ≤
      sprob (BacktrackGenFor.gen (P := fun p : HierMode × TypeEnv => GenTypeEnvB p.1 budget p.2)
        (G := SGen) s l) {p | 2 ≤ p.2.ets.toList.length ∧ 2 ≤ p.2.schema.environments.length} := by
  refine (genTypeEnvB_instance_varied budget s l hb).trans (sexpect_mono _ fun p => ?_)
  refine Set.indicator_le_indicator_of_subset ?_ (fun _ => zero_le) p
  rintro p ⟨h2, e₁, h₁, e₂, h₂, hne⟩
  exact ⟨h2, two_le_length_of_ne h₁ h₂ hne⟩

/-! ## Ancestor closures, for the whole generator -/

theorem single_branch_eq {b : Unit → SGen A} (hb : sok (b ()) = 1) (f : A → ℝ≥0∞) :
    sexpect (Specimen.Backtrack.backtrack [(1, b)]) f = sexpect (b ()) f := by
  rw [sexpect_backtrack_eq _ _ (by simp [sumWeights]) (by simpa using hb)]
  simp [sumWeights]

theorem single_branch_le_mul {b : Unit → SGen A} {f g : A → ℝ≥0∞} {c : ℝ≥0∞} (hb : sok (b ()) = 1)
    (h : sexpect (b ()) f ≤ c * sexpect (b ()) g) :
    sexpect (Specimen.Backtrack.backtrack [(1, b)]) f ≤ c * sexpect (Specimen.Backtrack.backtrack [(1, b)]) g := by
  rwa [single_branch_eq hb, single_branch_eq hb]

theorem sexpect_const_eq {g : SGen A} {f : A → ℝ≥0∞} {c : ℝ≥0∞} (hg : sok g = 1) (h : ∀ x, f x = c) :
    sexpect g f = c := by
  rw [sexpect_congr g h, sexpect_const', hg, one_mul]

/-- **Ancestor closures, for the schema generator as its instance runs it.** At leaf size `l`, over the schemas
it produces in the sparse mode with at least one standard entity type, the mean number of ancestors
of a uniformly chosen standard entity type (the size of its ancestor closure, itself not counted) is
at most `H(l + 1) - 1`. The size `s` plays no part: every part is drawn at the leaf size. -/
theorem genTypeEnvB_instance_sparse_mean (budget s l : Nat) :
    sexpect (BacktrackGenFor.gen (P := fun p : HierMode × TypeEnv => GenTypeEnvB p.1 budget p.2) (G := SGen) s l)
        (fun p => if p.1 = .sparse then ENNReal.ofReal (meanAnc p.2.ets.toList) else 0) ≤
      ENNReal.ofReal ((harmonic (l + 1) : ℝ) - 1) *
        sprob (BacktrackGenFor.gen (P := fun p : HierMode × TypeEnv => GenTypeEnvB p.1 budget p.2) (G := SGen) s l)
          {p | p.1 = .sparse ∧ 1 ≤ (ancStats p.2.ets.toList).2} := by
  by_cases hb : 1 ≤ budget
  · show sexpect (typeEnvGen (s + 1) l s budget) _ ≤ _ * sprob (typeEnvGen (s + 1) l s budget) _
    rw [typeEnvGen, (worker% gen SchemaGen.GenTypeEnvB [0, 2] eq_def)]
    have hE := entities1_sparse_mean l
    rcases s with _ | s <;> unfold sprob <;> apply single_branch_le_mul
    case hb | hb =>
      refine sok_bind_one_of_support (sok_we1 l l l) fun ⟨r, names, entries⟩ => fun hp => ?_
      have hne := wfEntitiesGo1_names_ne_nil
        ((worker% gen SchemaGen.WfEntitiesGo1 [0, 3, 4] sound)
          (l + 1) l l [] [] _ hp)
      exact sok_bind_one (sok_wa_top l l l r names actionEidPool budget hne
        (by simp [actionEidPool]) hb) fun _ => sok_pure _
    case h | h =>
      rw [sexpect_bind, sexpect_bind]
      refine le_of_eq_of_le (sexpect_congr_support ?_) (hE.trans_eq (congrArg _ (sexpect_congr_support ?_)))
      all_goals
        rintro ⟨r, names, entries⟩ hp
        have hne := wfEntitiesGo1_names_ne_nil
          ((worker% gen SchemaGen.WfEntitiesGo1 [0, 3, 4] sound)
            (l + 1) l l [] [] _ hp)
        have hwa := sok_wa_top l l l r names actionEidPool budget hne (by simp [actionEidPool]) hb
        dsimp only
        rw [sexpect_bind]
        first | refine sexpect_const_eq hwa ?_ | refine (sexpect_const_eq hwa ?_).symm
        rintro ⟨acts, reqty⟩
        simp [sexpect_pure, Set.indicator, Cedar.Data.Map.toList]
  · have h0 : ∀ x, ¬ Produces (BacktrackGenFor.gen (P := fun p : HierMode × TypeEnv => GenTypeEnvB p.1 budget p.2)
        (G := SGen) s l) x := fun ⟨r, env⟩ h => by
      have := Sound.genTypeEnvB_instance_generated budget s l r env h
      have := envCount_pos_of_wf this.1
      omega
    refine le_of_eq_of_le ?_ zero_le
    exact le_antisymm ((sexpect_mono_support fun x hx => (h0 x hx).elim).trans_eq (sexpect_zero_fun _)) zero_le

/-- …at most `ln (l + 1)`. -/
theorem genTypeEnvB_instance_sparse_mean_log (budget s l : Nat) :
    sexpect (BacktrackGenFor.gen (P := fun p : HierMode × TypeEnv => GenTypeEnvB p.1 budget p.2) (G := SGen) s l)
        (fun p => if p.1 = .sparse then ENNReal.ofReal (meanAnc p.2.ets.toList) else 0) ≤
      ENNReal.ofReal (Real.log (l + 1)) *
        sprob (BacktrackGenFor.gen (P := fun p : HierMode × TypeEnv => GenTypeEnvB p.1 budget p.2) (G := SGen) s l)
          {p | p.1 = .sparse ∧ 1 ≤ (ancStats p.2.ets.toList).2} := by
  refine (genTypeEnvB_instance_sparse_mean budget s l).trans ?_
  gcongr
  have := harmonic_sub_one_le_log (l + 1)
  push_cast at this
  exact this

end Cedar.Validation.Relational.SchemaGen.Sure

#print axioms Cedar.Validation.Relational.SchemaGen.Sure.genTypeEnvB_instance_sparse_mean_log
#print axioms Cedar.Validation.Relational.SchemaGen.Sure.genTypeEnvB_instance_varied
#print axioms Cedar.Validation.Relational.SchemaGen.Sure.genTypeEnvB_instance_varied_length
#print axioms Cedar.Validation.Relational.SchemaGen.Sure.genTypeEnvB_instance_sparse_mean
