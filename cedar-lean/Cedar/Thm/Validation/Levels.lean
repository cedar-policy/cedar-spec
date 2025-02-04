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

import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker.IfThenElse
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Types

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem entities_attrs_then_find? {entities: Entities} {attrs : Map Attr Value} {uid : EntityUID}
  (he : entities.attrs uid = .ok attrs)
  : ∃ ed, entities.find? uid = some ed ∧ ed.attrs = attrs
:= by sorry

theorem entities_find?_then_attrs {entities: Entities} {ed : EntityData} {uid : EntityUID}
  (he : entities.find? uid = some ed)
  : .ok ed.attrs = entities.attrs uid
:= by sorry

-- theorem entities_attrs_iff_find? {entities: Entities} {attrs : Map Attr Value} {uid : EntityUID}
--   : (entities.attrs uid = .ok attrs) ↔ (∃ ed, entities.find? uid = some ed ∧ ed.attrs = attrs)
-- := by sorry

theorem check_level_root_invariant (n n' : Nat) (e : TypedExpr)
  : (checkLevel e n).root = (checkLevel e n').root
:= by
  unfold checkLevel
  cases e <;> simp
  case ite | unaryApp =>
    simp [check_level_root_invariant n n']
  case binaryApp op _ _ _ =>
    cases op
    case mem | getTag | hasTag =>
      simp [check_level_root_invariant (n - 1) (n' - 1)]
    all_goals { simp [check_level_root_invariant n n'] }
  case getAttr e _ _ | hasAttr e _ _ =>
    cases e.typeOf
    case entity =>
      simp [check_level_root_invariant (n - 1) (n' - 1)]
    all_goals { simp [check_level_root_invariant n n'] }
  -- Hopefully should be trivial
  case set es _ | call es _ => sorry
  case record a => sorry

theorem check_level_succ {e : TypedExpr} {n : Nat}
  (h₁ : (checkLevel e n).checked)
  : (checkLevel e (1 + n)).checked
:= by
  cases e <;> try (simp [checkLevel] at h₁ ; simp [checkLevel])
  case ite | and | or | unaryApp =>
    simp [h₁, check_level_succ]
  case binaryApp op e₀ _ _ =>
    cases op <;> (
      simp [checkLevel] at h₁
      simp [checkLevel]
      simp [h₁, check_level_succ]
    )
    case mem | hasTag | getTag =>
      repeat constructor
      · have h₂ := check_level_root_invariant (1 + n - 1) (n - 1)
        simp [h₂, h₁]
      · omega
      · have h₂ : (1 + n - 1) = (1 + (n - 1)) := by omega
        simp [h₁, h₂, check_level_succ]
  case hasAttr e _ _ | getAttr e _ _ =>
    split at h₁
    · simp [checkLevel] at h₁
      simp [checkLevel]
      repeat constructor
      · have h₂ := check_level_root_invariant (1 + n - 1) (n - 1)
        simp [h₂, h₁]
      · omega
      · have h₂ : (1 + n - 1) = (1 + (n - 1)) := by omega
        simp [h₁, h₂, check_level_succ]
    · simp [h₁, check_level_succ]
  -- should be trivial
  case set | call => sorry
  case record => sorry

theorem slice_at_level_inner_succ {n: Nat} {work : Set EntityUID} {uid : EntityUID} {entities : Entities} {slice₀ slice₁ : Set EntityUID}
  (hs₀ : slice₀ = Entities.sliceAtLevel.sliceAtLevel entities work n)
  (hs₁ : slice₁ = Entities.sliceAtLevel.sliceAtLevel entities work (1 + n))
  (he₀ : uid ∈ slice₀ )
  : uid ∈ slice₁
:= by
  cases n
  case zero =>
    replace hs₀ : some slice₀ = some ∅ := by
      simp [hs₀, Entities.sliceAtLevel, Entities.sliceAtLevel.sliceAtLevel]
    injections hs₀
    rw [hs₀] at he₀
    contradiction
  case succ n =>
    unfold Entities.sliceAtLevel.sliceAtLevel at hs₀ hs₁
    simp at hs₀ hs₁
    have h₁ : (1 + (n + 1) - 1) = (1 + n) := by omega
    rw [h₁] at hs₁
    cases hm : List.mapM (Map.find? entities) work.elts <;> simp [hm] at hs₀ hs₁
    rename_i sliceₙ
    cases hrs₀ : (Entities.sliceAtLevel.sliceAtLevel entities (flatten_union (List.map EntityData.sliceEUIDs sliceₙ)) n) <;> simp [hrs₀] at hs₀
    cases hrs₁ : (Entities.sliceAtLevel.sliceAtLevel entities (flatten_union (List.map EntityData.sliceEUIDs sliceₙ)) (1 + n)) <;> simp [hrs₁] at hs₁
    rename_i slice₀' slice₁'
    subst slice₀ slice₁
    have ⟨ hi₀, _ ⟩ := Set.mem_union_iff_mem_or work slice₀' uid
    specialize hi₀ he₀
    cases hi₀
    case inl hi₀ =>
      have ⟨ _, hi₁ ⟩ := Set.mem_union_iff_mem_or work slice₁' uid
      simp [hi₁, hi₀]
    case inr hi₀ =>
      have ⟨ _, hi₁ ⟩ := Set.mem_union_iff_mem_or work slice₁' uid
      symm at hrs₀ hrs₁
      simp [hi₁, slice_at_level_inner_succ hrs₀ hrs₁ hi₀]

theorem slice_at_level_succ {n: Nat} {request : Request} {uid : EntityUID} {data : EntityData} {entities : Entities} {slice₀ slice₁ : Entities}
  (hs₀ : slice₀ = Entities.sliceAtLevel entities request n)
  (hs₁ : slice₁ = Entities.sliceAtLevel entities request (1 + n))
  (he₀ : slice₀.find? uid = some data)
  : slice₁.find? uid = some data
:= by sorry

theorem not_entities_attrs_then_not_slice_attrs {n: Nat} {request : Request} {uid : EntityUID} {e : Error} {entities slice : Entities}
  (hs : slice = Entities.sliceAtLevel entities request n)
  (hse : entities.attrs uid = .error e)
  : slice.attrs uid = .error e
:= by sorry

theorem typed_at_level_inversion {e : Expr} {c₀: Capabilities} {env : Environment} {n : Nat} :
  typedAtLevel e c₀ env n ->
  ∃ tx c₁, typeOf e c₀ env = .ok (tx, c₁) ∧ (checkLevel tx n).checked
:= by
  unfold typedAtLevel
  split
  · rename_i h₂
    rw [h₂]
    simp
  · simp

theorem typed_at_level_def {e : Expr} {tx : TypedExpr} {c₀ c₁: Capabilities} {env : Environment} {n : Nat} :
  typeOf e c₀ env = .ok (tx, c₁) → (checkLevel tx n).checked →
  typedAtLevel e c₀ env n
:= by
  intros h₁
  unfold typedAtLevel
  rw [h₁]
  simp

def TypedAtLevelIsSound (e : Expr) : Prop := ∀ {n : Nat} {c : Capabilities} {env :Environment} {request : Request} {entities slice : Entities},
  slice = entities.sliceAtLevel request n →
  CapabilitiesInvariant c request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typedAtLevel e c env n →
  evaluate e request entities = evaluate e request slice

theorem level_based_slicing_is_sound_if {c t e : Expr} {n : Nat} {c₀ c₁: Capabilities} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hc : CapabilitiesInvariant c₀ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (.ite c t e) c₀ env = Except.ok (tx, c₁))
  (h₄ : (checkLevel tx n).checked = true)
  (ihc : TypedAtLevelIsSound c)
  (iht : TypedAtLevelIsSound t)
  (ihe : TypedAtLevelIsSound e)
  : evaluate (.ite c t e) request entities = evaluate (.ite c t e) request slice
:= by
    have ⟨ty₁, bty₁, c₁, ty₂, c₂, ty₃, c₃, h₅, h₆, h₇, h₈ ⟩ := type_of_ite_inversion h₃
    have ⟨ hgc, v, h₁₃, h₁₄ ⟩ := type_of_is_sound hc h₂ h₆
    rw [h₇] at h₁₄
    split at h₈
    · replace ⟨h₇, h₈, h₉⟩ := h₈
      subst h₉
      replace h₁₄ := instance_of_ff_is_false h₁₄
      subst h₁₄
      rw [h₅] at h₄
      simp only [checkLevel, Bool.and_eq_true] at h₄
      have ⟨ ⟨ hl₄, _ ⟩,  hr₄⟩ := h₄
      specialize ihc hs hc h₂ (typed_at_level_def h₆ hl₄)
      specialize ihe hs hc h₂ (typed_at_level_def h₇ hr₄)
      simp only [evaluate]
      rw [ihc, ihe]
      cases h₁₂ : Result.as Bool (evaluate c request slice) <;> simp only [Except.bind_err, Except.bind_ok]
      simp only [Result.as, Coe.coe, Value.asBool] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq, Except.ok.injEq] at h₁₂
      subst h₁₂
      rename_i h₁₅
      simp only [EvaluatesTo, ihc, h₁₅, reduceCtorEq, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq, false_or] at h₁₃
      subst h₁₃
      simp
    · replace ⟨h₇, h₈, h₉⟩ := h₈
      subst h₉
      replace h₁₄ := instance_of_tt_is_true h₁₄
      subst h₁₄
      rw [h₅] at h₄
      simp only [checkLevel, Bool.and_eq_true] at h₄
      have ⟨ ⟨ hl₄, hr₄ ⟩,  _⟩ := h₄
      specialize ihc hs hc h₂ (typed_at_level_def h₆ hl₄)
      simp only [evaluate]
      rw [ihc]
      cases h₁₂ : Result.as Bool (evaluate c request slice) <;> simp only [Except.bind_err, Except.bind_ok]
      simp only [Result.as, Coe.coe, Value.asBool] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq, Except.ok.injEq] at h₁₂
      subst h₁₂
      rename_i h₁₅
      simp only [EvaluatesTo, ihc, h₁₅, reduceCtorEq, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq, false_or] at h₁₃
      subst h₁₃
      simp only [GuardedCapabilitiesInvariant, ihc, h₁₅, forall_const] at hgc
      specialize iht hs (capability_union_invariant hc hgc) h₂ (typed_at_level_def h₇ hr₄)
      simp [iht]
    · replace ⟨h₇, h₈, h₉, h₁₀⟩ := h₈
      rw [h₅] at h₄
      simp only [checkLevel, Bool.and_eq_true] at h₄
      have ⟨⟨ ha₄, hb₄ ⟩, hc₄ ⟩ := h₄
      specialize ihc hs hc h₂ (typed_at_level_def h₆ ha₄)
      specialize ihe hs hc h₂ (typed_at_level_def h₈ hc₄)
      simp only [ihc, ihe, evaluate]
      cases h₁₂ : Result.as Bool (evaluate c request slice) <;> simp only [Except.bind_err, Except.bind_ok]
      simp only [Result.as, Coe.coe, Value.asBool] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq, Except.ok.injEq] at h₁₂
      subst h₁₂
      rename_i h₁₄
      rename_i b ; cases b
      case false => simp
      case true =>
        simp only [GuardedCapabilitiesInvariant, ihc, h₁₄, forall_const] at hgc
        specialize iht hs (capability_union_invariant hc hgc) h₂ (typed_at_level_def h₇ hb₄)
        simp [iht]

theorem mapm_elem {α β: Type} {l : List α} {l' : List β} {f : α → Option β} {e: α}
  (h₁ : List.mapM f l = l')
  (h₂ : e ∈ l)
  : ∃ e', f e = some e' ∧ e' ∈ l'
:= by
  have ⟨ y, h₃, h₄ ⟩ := List.mapM_some_implies_all_some h₁ e h₂
  exists y

theorem mapm_pair_lookup  {α γ : Type} [BEq α] [LawfulBEq α] {l : List α} {l' : List (α × γ)} {f : α → Option (α × γ)} {e: α}
  (h₁ : List.mapM f l = some l')
  (h₂ : e ∈ l)
  (hf : ∀ e, match f e with
    | some e' => e'.fst = e
    | none => True)
  : ∃ e', f e = some e' ∧  l'.lookup e'.fst = some e'.snd
:= by
  cases l
  case nil => contradiction
  case cons h t =>
    cases h₃ : f h <;>
    cases h₄ : List.mapM f t <;>
    simp only [h₃, h₄, List.mapM_cons, Option.pure_def, Option.bind_none_fun, Option.bind_some_fun, Option.some.injEq, reduceCtorEq] at h₁
    subst h₁
    simp only [List.mem_cons] at h₂
    cases h₂
    case _ h₂ =>
      simp [h₂, h₃, List.lookup]
    case _ h₂ =>
      have ⟨ e'', ih₁, ih₂ ⟩ := mapm_pair_lookup h₄ h₂ hf
      have fh₁ := hf h ; rw [h₃] at fh₁ ; subst fh₁
      have fh₂ := hf e ; rw [ih₁] at fh₂ ; subst fh₂
      simp only [ih₁,ih₂, Option.some.injEq, List.lookup, exists_eq_left']
      split
      · rename_i h₅
        simp only [beq_iff_eq] at h₅
        simp only [←h₅, ih₁, Option.some.injEq] at h₃
        rw [h₃]
      · simp

theorem euid_in_work_then_in_slice
  (hw : euid ∈ work)
  (hs : some slice = Entities.sliceAtLevel.sliceAtLevel entities work n)
  (hn : n > 0)
  : euid ∈ slice
:= by
  unfold Entities.sliceAtLevel.sliceAtLevel at hs
  split at hs
  case isTrue hn' =>
    replace hn : (n == 0) = false :=
      by simp only [beq_eq_false_iff_ne, ne_eq]; omega
    simp [hn] at hn'
  case isFalse =>
    cases h₁ :
      List.mapM (Map.find? entities) work.elts
    <;> simp [h₁] at hs
    rename_i eds
    cases h₂ :
      List.mapM (fun x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs (n - 1)) eds
    <;> simp [h₂] at hs
    rename_i slice'
    subst hs
    have ⟨ _, hc ⟩ := Set.mem_union_iff_mem_or work (flatten_union slice') euid
    apply hc
    simp [hw]

/-
theorem slice_at_zero_empty_inner
  (hs : some slice = Entities.sliceAtLevel.sliceAtLevel entities work 0)
  : slice = ∅
:= by
  simp only [Entities.sliceAtLevel.sliceAtLevel, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hs
  exact hs

theorem slice_at_zero_empty {request : Request} {entities slice : Entities}
  (hs : some slice = Entities.sliceAtLevel entities request 0)
  : slice = Map.empty
:= by
  simp [Entities.sliceAtLevel] at hs
  cases h₁ : Entities.sliceAtLevel.sliceAtLevel entities request.sliceEUIDs 0 <;> simp [h₁] at hs
  symm at h₁
  simp [hs, slice_at_zero_empty_inner h₁, Map.empty, Map.make, List.canonicalize]
-/

/--
theorem slice_at_1_has_entity_inner
  {e: Expr} {tx : TypedExpr} {c c' : Capabilities} {env : Environment} {request : Request} {work : Set EntityUID} {euid : EntityUID} {data : EntityData} {entities : Entities} {slice : List (EntityUID × EntityData)}
  (hs : slice = Entities.sliceAtLevel.sliceAtLevel entities work 1)
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : checkLevel tx 0 = LevelCheckResult.mk true true)
  (he : evaluate e request entities = Except.ok (Value.prim (Prim.entityUID euid)))
  (hf : entities.find? euid = .some data) :
  slice.lookup euid = .some data
:= by
  cases e
  case lit =>
    simp [evaluate] at he
    subst he
    simp [typeOf] at ht
    unfold typeOfLit at ht
    simp only at ht
    cases h₁ : (env.ets.contains euid.ty || env.acts.contains euid)
    · simp [h₁, err] at ht
    · simp [h₁, ok] at ht
      simp [checkLevel, ←ht] at hl
  case var v => sorry
  /-
    cases v <;> simp [evaluate] at he <;> subst he
    all_goals {
      simp [Entities.sliceAtLevel.sliceAtLevel] at hs
      have ⟨ e'', h₂, h₃⟩ := mapm_pair_lookup hs hw
      simp [hf] at h₂
      subst h₂
      simp at h₃
      exact h₃
    }
  -/
  case ite i t e =>
    have ⟨ty₁, bty₁, c₁, ty₂, c₂, ty₃, c₃, h₂, h₃, h₄, h₅ ⟩ := type_of_ite_inversion ht
    have hmk : ∀ r, r = LevelCheckResult.mk r.checked r.root := by simp
    have hl₂ : checkLevel ty₂ 0 = { checked := true, root := true } := by
      rw [hmk (checkLevel ty₂ 0)]
      rw [h₂] at hl
      simp only [checkLevel, LevelCheckResult.mk.injEq,Bool.and_eq_true] at hl
      simp [hl]
    have hl₃ : checkLevel ty₃ 0 = { checked := true, root := true } := by
      rw [hmk (checkLevel ty₃ 0)]
      rw [h₂] at hl
      simp only [checkLevel, LevelCheckResult.mk.injEq,Bool.and_eq_true] at hl
      simp [hl]
    simp [evaluate] at he
    cases h₁ : Result.as Bool (evaluate i request entities) <;> simp [h₁] at he
    split at he
    case isTrue =>
      split at h₅
      · sorry
      · replace ⟨ h₅, _, _ ⟩ := h₅
        have huc : CapabilitiesInvariant (c ∪ c₁) request entities := by sorry
        exact slice_at_1_has_entity_inner hs huc hr h₅ hl₂ he hf
      · replace ⟨ h₅, _, _, _ ⟩ := h₅
        have huc : CapabilitiesInvariant (c ∪ c₁) request entities := by sorry
        exact slice_at_1_has_entity_inner hs huc hr h₅ hl₂ he hf
    case isFalse =>
      split at h₅
      · replace ⟨ h₅, _, _ ⟩ := h₅
        exact slice_at_1_has_entity_inner hs hc hr h₅ hl₃ he hf
      · sorry
      · replace ⟨ _, h₅, _, _ ⟩ := h₅
        exact slice_at_1_has_entity_inner hs hc hr h₅ hl₃ he hf
  case and => sorry
  case or => sorry
  case unaryApp o e =>
    simp [evaluate, apply₁] at he
    cases h₁ : evaluate e request entities <;> simp [h₁] at he
    split at he <;> try simp at he
    simp [intOrErr] at he
    split at he <;> simp at he
  case binaryApp => sorry
  case getAttr e a =>
    have ⟨ _, _, _, _, h₁, h₂ ⟩ := type_of_getAttr_inversion ht
    cases h₂
    · rename_i h₂ ; replace ⟨ _, h₂⟩ := h₂
      rw [h₁] at hl
      simp [checkLevel, h₂] at hl
    · sorry
  case hasAttr => sorry
  case set => sorry
  case record => sorry
  case call => sorry
--/

def ReachableIn (es : Entities) (start : Set EntityUID) (finish : EntityUID) (level : Nat) : Prop :=
    if level == 0 then False else
      finish ∈ start ∨
        ∃ uid ∈ start, ∃ ed,
          some ed  = es.find? uid ∧
          ReachableIn es ed.sliceEUIDs finish (level - 1)
    termination_by level
    decreasing_by
      rename_i h₁
      simp only [beq_iff_eq] at h₁
      omega

def EuidInValue (v : Value) (path : List Attr) (euid : EntityUID) : Prop :=
  match path with
  | [] =>
    match v with
    | .prim (.entityUID euid') => euid' = euid
    | _ => False
  | a :: path' =>
    match v with
    | .record attrs =>
      match attrs.find? a with
      | .some v' => EuidInValue v' path' euid
      | .none => False
    | _ => False

theorem mapm_mem
  (h₁ : some l' = List.mapM f l)
  (h₂ : e ∈ l)
  :  ∃ e', some e' = f e ∧ e' ∈ l'
:= by sorry

theorem mem_flatten_union_iff_mem_any {α : Type} [LT α] [DecidableLT α] {ll : List (Set α)} {e : α}
  : e ∈ flatten_union ll ↔ ∃ l ∈ ll, e ∈ l
:= by sorry

theorem slice_contains_reachable
  {n: Nat}
  {work : Set EntityUID} {euid : EntityUID} {entities : Entities} {slice : Set EntityUID}
  (hw : ReachableIn entities work euid (1 + n))
  (hs : some slice = Entities.sliceAtLevel.sliceAtLevel entities work (1 + n))
  (h₅ : entities.contains euid) :
  euid ∈ slice
:= by
  cases n
  case zero =>
    simp [ReachableIn] at hw
    exact euid_in_work_then_in_slice hw hs (by simp)
  case succ =>
    unfold ReachableIn at hw
    simp at hw
    cases hw
    case inl hw =>
      exact euid_in_work_then_in_slice hw hs (by omega)
    case inr hw =>
      replace ⟨ euid', hi, ed, hf, hw ⟩ := hw
      rename_i n'
      have h₆ : (1 + (n' + 1) - 1) = 1 + n' := by omega
      rw [h₆] at hw
      unfold Entities.sliceAtLevel.sliceAtLevel at hs
      simp at hs
      cases h₇ : (List.mapM (Map.find? entities) work.elts) <;> simp [h₇] at hs
      rename_i eds
      cases h₈ : Option.map flatten_union (List.mapM (fun x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs (1 + (n' + 1) - 1)) eds) <;> simp [h₈] at hs
      subst hs
      rename_i slice'
      cases h₉ : List.mapM (fun x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs (1 + (n' + 1) - 1)) eds <;> simp [h₉] at h₈
      subst h₈
      rw [Set.mem_union_iff_mem_or]
      right
      symm at h₇
      have ⟨ e', h₁₀, h₁₁⟩ := mapm_mem h₇ hi
      rw [←h₁₀] at hf
      injections hf
      subst hf
      cases h₁₂ : (Entities.sliceAtLevel.sliceAtLevel entities ed.sliceEUIDs (1 + n'))
      case none =>
        -- `ed ∈ eds` by `h11` and we know mapm of this over all elements `eds`
        -- is `some`, so this element must be `some`
        sorry
      case some =>
        symm at h₁₂
        have ih := slice_contains_reachable hw h₁₂ h₅
        rw [h₆] at h₉
        rename_i ed_slice
        symm at h₉
        have ⟨ e'', h₁₃, h₁₄⟩ := mapm_mem h₉ h₁₁
        rw [←h₁₃] at h₁₂
        injections h₁₂
        subst h₁₂
        rw [mem_flatten_union_iff_mem_any]
        exists ed_slice

theorem map_find_mapm_value {α β : Type} [LT α] [DecidableLT α] [BEq α] {ks : Set α} {k : α} {kvs : List (α × β)} {fn : α → Option β}
  (h₁ : some kvs = List.mapM (λ k => (fn k).bind λ v => (some (k, v))) ks.elts)
  (h₂ : k ∈ ks)
  : (Map.make kvs).find? k = fn k
:= by
  cases h₃ : ks.elts
  case nil =>
    have hcontra : List.Mem k [] := by
      simp only [Membership.mem, h₃] at h₂
      exact h₂
    contradiction
  case cons h t =>
    simp [h₃] at h₁
    cases h₄ : ((fn h).bind fun v => some (h, v)) <;> simp [h₄] at h₁
    cases h₅ : (List.mapM (fun k => (fn k).bind fun v => some (k, v)) t) <;> simp [h₅] at h₁
    subst h₁
    simp only [Membership.mem, h₃] at h₂
    cases h₂
    case head =>
      cases h₆ : (fn k) <;> simp [h₆] at h₄
      subst h₄
      sorry
    case tail h₂ =>
      symm at h₅
      sorry

theorem attrs_then_find {entities : Entities} {euid : EntityUID} :
  (entities.attrs euid).isOk → entities.contains euid
:= by sorry

theorem reachable_succ {n : Nat} {euid : EntityUID} {start : Set EntityUID} {entities : Entities}
  (hr : ReachableIn entities start euid n)
  : ReachableIn entities start euid (1 + n)
:= by
  unfold ReachableIn at hr ⊢
  split at hr
  · contradiction
  · rename_i hn
    have hsn : ((1 + n == 0) = true) = False := by simp
    simp only [hsn, ↓reduceIte]
    cases hr
    case inl hr => simp [hr]
    case inr hr =>
      right
      have ⟨ euid', hs, ed', hrl, hrr ⟩ := hr ; clear hr
      exists euid'
      simp only [hs, true_and]
      exists ed'
      simp only [hrl, true_and]
      simp only [beq_iff_eq] at hn
      have hterm : n - 1 < n := by omega
      have ih := reachable_succ hrr
      replace hn : (1 + n - 1) = (1 + (n - 1)) := by omega
      simp [hn, ih]
termination_by n

theorem reachable_ancestor_step {n : Nat} {euid euid' : EntityUID} {start : Set EntityUID} {entities : Entities} {ed : EntityData}
  (hr : ReachableIn entities start euid n)
  (he : .some ed = entities.find? euid)
  (he' : euid' ∈ ed.ancestors) :
  ReachableIn entities start euid' (1 + n)
:= by sorry

theorem reachable_tag_step {n : Nat} {euid euid' : EntityUID} {start : Set EntityUID} {entities : Entities} {ed : EntityData} {t : Tag}
  (hr : ReachableIn entities start euid n)
  (he : .some ed = entities.find? euid)
  (he' : .some (.prim (.entityUID euid')) = ed.tags.find? t) :
  ReachableIn entities start euid' (1 + n)
:= by sorry

theorem reachable_attr_step {n : Nat} {euid euid' : EntityUID} {start : Set EntityUID} {entities : Entities} {ed : EntityData} {a : Attr}
  (hr : ReachableIn entities start euid n)
  (he₁: .some ed = entities.find? euid)
  (he₂ : .some v = ed.attrs.find? a)
  (he₃ : ∃ path, EuidInValue v path euid' ) :
  -- (he' : .some (.prim (.entityUID euid')) = ed.attrs.find? a) :
  ReachableIn entities start euid' (1 + n)
:= by
  unfold ReachableIn at hr ⊢
  split at hr
  · contradiction
  · rename_i hn
    have hsn : ((1 + n == 0) = true) = False := by simp
    simp only [hsn, ↓reduceIte]
    cases hr
    case inl hr =>
      right
      exists euid
      simp only [hr, true_and]
      exists ed
      simp only [he₁, true_and]
      have hn' : (1 + n - 1) = n := by omega
      rw [hn']
      unfold ReachableIn
      simp only [hn, Bool.false_eq_true, ↓reduceIte]
      left
      unfold EntityData.sliceEUIDs
      rw [Set.mem_union_iff_mem_or]
      left
      rw [mem_flatten_union_iff_mem_any]
      exists (Value.prim (Prim.entityUID euid')).sliceEUIDs
      constructor
      case left =>
        simp
        exists Value.prim (Prim.entityUID euid')
        simp only [and_true]
        -- If exists `a` where `ed.attrs.find? a` is `some v` (`he'`) then `v` in `ed.attrs.values`
        sorry
      case right =>
        simp [Value.sliceEUIDs, Set.mem_singleton]
    case inr hr =>
      have ⟨ euid'', hs, ed'', hrl, hrr ⟩ := hr ; clear hr
      right
      exists euid''
      simp only [hs, true_and]
      exists ed''
      simp only [hrl, true_and]
      have hn' : (1 + n - 1) = (1 + (n - 1)) := by simp at hn; omega
      rw [hn']
      exact reachable_attr_step hrr he₁ he₂ he₃

theorem in_val_then_val_slice
  (hv : EuidInValue v path euid)
  : euid ∈ v.sliceEUIDs
:= by
  cases v
  case prim p =>
    unfold EuidInValue at hv
    cases p
    case entityUID =>
      split at hv <;> simp only at hv
      simp [hv, Value.sliceEUIDs, Set.mem_singleton]
    all_goals { split at hv <;> contradiction }
  case record attrs =>
    unfold EuidInValue at hv
    split at hv <;> simp at hv
    rename_i path a path'
    split at hv <;> try contradiction
    rename_i v ha
    have ih := in_val_then_val_slice hv
    simp [Value.sliceEUIDs]
    rw [mem_flatten_union_iff_mem_any]
    exists v.sliceEUIDs
    simp only [ih, List.mem_map, Subtype.exists, Prod.exists, and_true]
    exists a, v
    simp [Map.find?_mem_toList, ha]
  case set | ext =>
    unfold EuidInValue at hv
    split at hv <;> split at hv <;>
    ( rename_i hv' ; simp at hv hv' )

theorem slice_at_succ_n_reachable {e : Expr} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {entities : Entities}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : checkLevel tx n = LevelCheckResult.mk true true)
  (he : evaluate e request entities = .ok v)
  (ha : ∃ attrs, EuidInValue v attrs euid )
  (hf : entities.contains euid) :
  ReachableIn entities request.sliceEUIDs euid (1 + n)
:= by
  cases e
  case lit =>
    simp [evaluate] at he
    subst he
    unfold EuidInValue at ha
    replace ⟨ attrs, ha ⟩ := ha
    split at ha <;> try simp at ha
    split at ha <;> try simp at ha
    subst ha
    rename_i hp
    injections hp
    subst hp
    simp [typeOf, typeOfLit] at ht
    split at ht
    case isTrue =>
      simp [ok] at ht
      replace ⟨ ht, hc' ⟩ := ht
      subst ht hc'
      simp [checkLevel] at hl
    case isFalse =>
      simp [err] at ht
  case var v =>
    cases v <;> simp [evaluate] at he
    case context =>
      subst he
      unfold ReachableIn
      simp
      left
      rw [Request.sliceEUIDs, Set.mem_union_iff_mem_or, ←Set.make_mem]
      right
      simp [Value.sliceEUIDs]
      unfold EuidInValue at ha
      replace ⟨ attrs, ha ⟩ := ha
      simp at ha
      split at ha <;> try contradiction
      split at ha <;> try contradiction
      rename_i hctx
      have ha' := in_val_then_val_slice ha
      rename_i a _ _ v
      rw [mem_flatten_union_iff_mem_any]
      exists v.sliceEUIDs
      simp [ha']
      exists a, v
      simp
      exact Map.find?_mem_toList hctx
    all_goals {
      subst he
      unfold ReachableIn
      rw [Request.sliceEUIDs, Set.mem_union_iff_mem_or, ←Set.make_mem]
      unfold EuidInValue at ha
      replace ⟨ attrs, ha ⟩ := ha
      split at ha <;> try contradiction
      simp [ha]
    }
  case getAttr e a =>
    simp [evaluate] at he
    cases h₁ : evaluate e request entities <;> simp [h₁] at he
    have ⟨ hc', tx', c₁', ht', htx, h₂ ⟩ := type_of_getAttr_inversion ht
    subst hc'
    rw [htx] at hl
    simp only [checkLevel, gt_iff_lt] at hl
    have ⟨ hgc, v, he', hi ⟩ := type_of_is_sound hc hr ht'
    split at hl
    · rename_i hety
      simp at hl
      have ⟨⟨⟨hl₀, hl₁⟩, hl₂⟩, hl₃⟩ := hl ; clear hl
      have hl' : checkLevel tx' (n - 1) = LevelCheckResult.mk true true := by
        have h : ∀ r, r = LevelCheckResult.mk r.checked r.root := by simp
        rw [h (checkLevel tx' (n - 1))]
        simp [hl₂, hl₃]
      rw [hety] at hi
      have ⟨ euid', hety, hv⟩  := instance_of_entity_type_is_entity hi
      subst hety hv
      unfold EvaluatesTo at he'
      rw [h₁] at he'
      cases he' <;> rename_i he' <;> simp at he'
      subst he'

      simp [getAttr, attrsOf] at he
      cases h₅ : entities.attrs euid' <;> simp [h₅] at he
      rename_i attrs
      simp [Map.findOrErr] at he
      split at he <;> simp at he
      subst he
      rename_i v hv

      have ⟨ ed, hed, hed' ⟩ := entities_attrs_then_find? h₅
      subst attrs
      have hf' : entities.contains euid' := by simp [Map.contains, Option.isSome, hed]

      have ih := slice_at_succ_n_reachable hc hr ht' hl' h₁ (by exists []) hf'
      have h₆ : (1 + (n - 1)) = n := by omega
      rw [h₆] at ih ; clear h₆

      symm at hv hed
      apply reachable_attr_step ih hed hv ha

    · rename_i hty
      cases h₂ <;> rename_i h₂
      · replace ⟨ ety, h₂ ⟩ := h₂
        specialize hty ety h₂
        contradiction
      · replace ⟨ rty, h₂ ⟩ := h₂
        clear hty
        rw [h₂] at hi
        have ⟨ attrs, hv⟩ := instance_of_record_type_is_record hi ; clear hi
        subst hv
        unfold EvaluatesTo at he'
        rw [h₁] at he'
        cases he' <;> rename_i he' <;> simp at he'
        subst he'
        simp [getAttr, attrsOf, Map.findOrErr] at he
        split at he <;> simp at he
        rename_i v hv
        subst he
        replace ⟨ path, ha ⟩ := ha
        have ha' : ∃ path', EuidInValue (Value.record attrs) path' euid := by
          exists a :: path
          simp [EuidInValue, hv, ha]
        exact slice_at_succ_n_reachable hc hr ht' hl h₁ ha' hf
  all_goals { sorry }

-- Because e typechecked and was annotated as ty₁ which then level checked
-- at level (n - 1), we know that `euid` is the result of at most `n - 1`
-- dereferences. `slice` was taken from `entities` at level `n`, so we can
-- do at least one more dereference without error.
theorem slice_at_succ_n_has_entity  {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {slice entities : Entities} {ed : EntityData}
  (hs : slice = Entities.sliceAtLevel entities request (1 + n))
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : checkLevel tx n = LevelCheckResult.mk true true)
  (he : evaluate e request entities = .ok (Value.prim (Prim.entityUID euid)))
  (hf : entities.find? euid = some ed) :
  slice.find? euid = some ed
:= by
  simp [Entities.sliceAtLevel] at hs
  cases h₁ : Entities.sliceAtLevel.sliceAtLevel entities request.sliceEUIDs (1 + n)  <;> simp [h₁] at hs
  rename_i eids
  cases h₂ : (List.mapM (fun e => (Map.find? entities e).bind fun __do_lift => some (e, __do_lift)) eids.elts)  <;> simp [h₂] at hs
  subst hs
  cases e
  case lit =>
    simp [evaluate] at he
    subst he
    simp [typeOf, typeOfLit] at ht
    split at ht
    case isTrue =>
      simp [ok] at ht
      replace ⟨ ht, hc' ⟩ := ht
      subst ht hc'
      simp [checkLevel] at hl
    case isFalse =>
      simp [err] at ht
  case var v =>
    cases v <;> simp [evaluate] at he
    all_goals {
      have hw : ReachableIn entities request.sliceEUIDs euid (1 + n) := by
        unfold ReachableIn ; simp
        left
        simp [←he, Request.sliceEUIDs]
        rw [Set.mem_union_iff_mem_or]
        left
        rw [←Set.make_mem]
        simp
      subst he
      symm at h₁
      have hi := slice_contains_reachable hw h₁ (by simp [hf, Map.contains_iff_some_find?])
      rw [←hf]
      symm at h₂
      exact map_find_mapm_value h₂ hi
    }
  case getAttr e a =>
    have hv : ∃ path, EuidInValue (Value.prim (Prim.entityUID euid)) path euid := by exists []
    have hf' : Map.contains entities euid := by simp [Map.contains, hf]
    have hw : ReachableIn entities request.sliceEUIDs euid (1 + n) :=
      slice_at_succ_n_reachable hc hr ht hl he hv hf'
    symm at h₁
    have hi := slice_contains_reachable hw h₁ (by simp [hf, Map.contains_iff_some_find?])
    rw [←hf]
    symm at h₂
    exact map_find_mapm_value h₂ hi
  all_goals { sorry }

theorem level_based_slicing_is_sound {e : Expr} {n : Nat} {c : Capabilities} {env : Environment} {request : Request} {slice entities : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hc : CapabilitiesInvariant c request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₁ : typedAtLevel e c env n) :
  evaluate e request entities = evaluate e request slice
:= by
  replace ⟨_, _, h₃, h₁⟩ := typed_at_level_inversion h₁
  cases e
  case lit => simp [evaluate]
  case var v => cases v <;> simp [evaluate]
  case ite c t e =>
    have ihc := @level_based_slicing_is_sound c
    have iht := @level_based_slicing_is_sound t
    have ihe := @level_based_slicing_is_sound e
    apply level_based_slicing_is_sound_if hs hc h₂ h₃ h₁ ihc iht ihe
  case and => sorry -- inductive case, similar ast rewriting concerns as `if`
  case or => sorry -- inductive case, similar ast rewriting concerns as `if`
  case unaryApp => sorry -- trivial inductive cases
  case binaryApp => sorry -- includes tags cases which should follow the attr cases and `in` case which might be tricky
  case getAttr e a =>
    have ⟨ h₇, ty₁, c₁', h₄, h₅, h₆ ⟩ := type_of_getAttr_inversion h₃
    subst h₇
    cases h₆
    case _ h₇ =>
      replace ⟨ ety, h₇⟩ := h₇
      have ⟨ hgc, v, h₁₃, h₁₄ ⟩ := type_of_is_sound hc h₂ h₄
      rw [h₇] at h₁₄
      replace ⟨ euid, h₁₄, h₁₅⟩ := instance_of_entity_type_is_entity h₁₄
      subst h₁₄ h₁₅
      rw [h₅] at h₁
      simp [checkLevel, h₇] at h₁
      have ⟨ ⟨ hll₁, hl₁⟩, hr₁ ⟩ := h₁ ; clear h₁
      have h₈ := check_level_succ hr₁
      have h₉ : (1 + (n - 1)) = n := by omega
      rw [h₉] at h₈ ; clear h₉
      simp [evaluate]
      rw [←level_based_slicing_is_sound hs hc h₂ (typed_at_level_def h₄ h₈)]
      clear h₈
      simp [getAttr, attrsOf]
      unfold EvaluatesTo at h₁₃
      rcases h₁₃ with h₁₃ | h₁₃ | h₁₃ | h₁₃ <;> simp [h₁₃]
      cases hee : entities.attrs euid
      case error => simp [not_entities_attrs_then_not_slice_attrs hs hee]
      case ok =>
        have h₆ : (checkLevel ty₁ (n - 1) = LevelCheckResult.mk true true) := by
          have h₇ : ∀ r, r = LevelCheckResult.mk r.checked r.root := by simp
          rw [h₇ (checkLevel ty₁ (n - 1))]
          simp [hr₁, hll₁]
        have h₈ : n = 1 + (n - 1) := by omega
        rw [h₈] at hs

        have ⟨ ed, hee', hee''⟩ := entities_attrs_then_find? hee
        subst hee''
        have h₇ := slice_at_succ_n_has_entity hs hc h₂ h₄ h₆ h₁₃ hee'
        replace h₇ := entities_find?_then_attrs h₇
        simp [h₇]
    case _ h₇  => sorry -- record case for `getAttr`
  case hasAttr => sorry -- should follow `getAttr`
  case set => sorry -- trivial recursive case maybe a little tricky
  case record => sorry -- likely to be tricky. Record cases are always hard, and here there might be an odd interaction with attribute access
  case call => sorry -- should be the same as set
