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
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Typechecker.Basic

namespace Cedar.Thm

/-!
This file contains useful definitions and lemmas about the level checking functions
-/

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem set_mem_flatten_union_iff_mem_any {α : Type} [LT α] [DecidableLT α] {ll : List (Set α)} {e : α}
  : e ∈ flatten_union ll ↔ ∃ l ∈ ll, e ∈ l
:= by sorry

theorem entities_attrs_then_find? {entities: Entities} {attrs : Map Attr Value} {uid : EntityUID}
  (he : entities.attrs uid = .ok attrs)
  : ∃ ed, entities.find? uid = some ed ∧ ed.attrs = attrs
:= by sorry

theorem entities_find?_then_attrs {entities: Entities} {ed : EntityData} {uid : EntityUID}
  (he : entities.find? uid = some ed)
  : .ok ed.attrs = entities.attrs uid
:= by sorry

theorem entities_tags_then_find? {entities: Entities} {tags : Map Tag Value} {uid : EntityUID}
  (he : entities.tags uid = .ok tags)
  : ∃ ed, entities.find? uid = some ed ∧ ed.tags = tags
:= by sorry

theorem entities_find?_then_tags {entities: Entities} {ed : EntityData} {uid : EntityUID}
  (he : entities.find? uid = some ed)
  : .ok ed.tags = entities.tags uid
:= by sorry

theorem map_find_then_value {α β : Type} [BEq α] {m : Map α β} {k : α} {v : β}
  (hf : m.find? k = some v)
  : v ∈ m.values
:= by sorry

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
    cases h₄ : ((fn h).bind λ v => some (h, v)) <;> simp [h₄] at h₁
    cases h₅ : (List.mapM (λ k => (fn k).bind λ v => some (k, v)) t) <;> simp [h₅] at h₁
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

theorem not_entities_then_not_slice_inner {n: Nat}  {uid : EntityUID} {e : Error} {entities : Entities} {work slice : Set EntityUID}
  (hs : some slice = Entities.sliceAtLevel.sliceAtLevel entities work n)
  (hne : entities.find? uid = none)
  (hnw : uid ∉ work)
  : uid ∉ slice
:= by
  unfold Entities.sliceAtLevel.sliceAtLevel at hs
  split at hs
  · injections hs
    subst hs
    intro
    contradiction
  · cases h₁ : (List.mapM (Map.find? entities) work.elts) <;> simp [h₁] at hs
    rename_i eds
    cases h₂ : (List.mapM (λ x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs (n - 1)) eds) <;> simp [h₂] at hs
    subst hs
    rw [Set.mem_union_iff_mem_or]
    intros hm
    cases hm
    case inl hl => contradiction
    case inr hr =>
      rw [set_mem_flatten_union_iff_mem_any] at hr
      have ⟨ e, hrl, hrr ⟩ := hr ; clear hr
      rename_i slice'
      sorry

theorem not_entities_then_not_slice {n: Nat} {request : Request} {uid : EntityUID} {entities slice : Entities}
  (hs : some slice = Entities.sliceAtLevel entities request n)
  (hse : entities.find? uid = none)
  : slice.find? uid = none
:= by sorry

theorem not_entities_attrs_then_not_slice_attrs {n: Nat} {request : Request} {uid : EntityUID} {e : Error} {entities slice : Entities}
  (hs : slice = Entities.sliceAtLevel entities request n)
  (hse : entities.attrs uid = .error e)
  : slice.attrs uid = .error e
:= by
  simp [Entities.attrs, Map.findOrErr] at hse ⊢
  split at hse <;> simp at hse
  rename_i h₁
  cases h₂ : entities.find? uid <;> simp [h₂] at h₁
  simp [hse, not_entities_then_not_slice hs h₂]

inductive ReachableIn : Entities → Set EntityUID → EntityUID → Nat → Prop where
  | in_start {es : Entities} {start : Set EntityUID} {finish : EntityUID} {level : Nat}
    (hs : finish ∈ start) :
    ReachableIn es start finish (Nat.succ level)
  | step {es : Entities} {start : Set EntityUID} {finish : EntityUID} {level : Nat} {ed : EntityData}
    (i : EntityUID)
    (hi : i ∈ start)
    (he : some ed = es.find? i)
    (hr : ReachableIn es ed.sliceEUIDs finish level) :
    ReachableIn es start finish (Nat.succ level)

inductive EuidInValue : Value → List Attr → EntityUID → Prop where
  | euid (euid : EntityUID) :
    EuidInValue (.prim (.entityUID euid)) [] euid
  | record {a : Attr} {path : List Attr} {attrs : Map Attr Value}
    (ha : attrs.find? a = some v)
    (hv : EuidInValue v path euid) :
    EuidInValue (.record attrs)  (a :: path) euid

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
      List.mapM (λ x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs (n - 1)) eds
    <;> simp [h₂] at hs
    rename_i slice'
    subst hs
    have ⟨ _, hc ⟩ := Set.mem_union_iff_mem_or work (flatten_union slice') euid
    apply hc
    simp [hw]

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
    cases hw
    case step hw => cases hw
    case in_start hw =>
      exact euid_in_work_then_in_slice hw hs (by simp)
  case succ =>
    cases hw
    case in_start hw =>
      exact euid_in_work_then_in_slice hw hs (by omega)
    case step n' ed euid' hf hi hw =>
      unfold Entities.sliceAtLevel.sliceAtLevel at hs
      simp at hs
      cases h₇ : (List.mapM (Map.find? entities) work.elts) <;> simp [h₇] at hs
      rename_i eds
      cases h₈ : Option.map flatten_union (List.mapM (λ x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs (1 + (n' + 1) - 1)) eds) <;> simp [h₈] at hs
      subst hs
      rename_i slice'
      cases h₉ : List.mapM (λ x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs (1 + (n' + 1) - 1)) eds <;> simp [h₉] at h₈
      subst h₈
      rw [Set.mem_union_iff_mem_or]
      right
      have ⟨ e', h₁₀, h₁₁⟩ := List.mapM_some_implies_all_some h₇ _ hi
      have h₆ : (1 + (n' + 1) - 1) = 1 + n' := by omega
      rw [h₆] at h₉
      have ⟨ slice, _, hs ⟩ := List.mapM_some_implies_all_some h₉ _ h₁₀
      rw [h₁₁] at hf ; injections hf ; subst hf
      cases h₁₂ : (Entities.sliceAtLevel.sliceAtLevel entities ed.sliceEUIDs (1 + n'))
      case none => simp [h₁₂] at hs
      case some =>
        symm at h₁₂
        have ih := slice_contains_reachable hw h₁₂ h₅
        rename_i ed_slice
        rw [hs] at h₁₂
        injections h₁₂
        subst h₁₂
        rw [set_mem_flatten_union_iff_mem_any]
        exists ed_slice

theorem reachable_succ {n : Nat} {euid : EntityUID} {start : Set EntityUID} {entities : Entities}
  (hr : ReachableIn entities start euid n)
  : ReachableIn entities start euid (1 + n)
:= by
  cases hr
  case in_start hi =>
    exact ReachableIn.in_start hi
  case step euid' hf hi hr =>
    exact ReachableIn.step euid' hi hf (reachable_succ hr)

theorem in_val_then_val_slice
  (hv : EuidInValue v path euid)
  : euid ∈ v.sliceEUIDs
:= by
  cases v
  case prim p =>
    cases hv
    simp [Value.sliceEUIDs, Set.mem_singleton]
  case record attrs =>
    cases hv
    rename_i v a path' ha hv
    have ih := in_val_then_val_slice hv
    simp [Value.sliceEUIDs]
    rw [set_mem_flatten_union_iff_mem_any]
    exists v.sliceEUIDs
    simp only [ih, List.mem_map, Subtype.exists, Prod.exists, and_true]
    exists a, v
    simp [Map.find?_mem_toList, ha]
  case set | ext => cases hv

theorem euid_not_in_not_entity_or_record (v : Value)
  (hv : match v with
    | .record _ => False
    | .prim (.entityUID _) => False
    | _ => True)
  : ∀ path euid, ¬ EuidInValue v path euid
:= by
  intro _ euid hv'
  split at hv <;> try contradiction
  rename_i hr he
  cases hv'
  · simp [he euid]
  · rename_i attrs _ _
    simp [hr attrs]

theorem reachable_tag_step {n : Nat} {euid euid' : EntityUID} {start : Set EntityUID} {entities : Entities} {ed : EntityData} {tag : Tag} {path : List Attr}
  (hr : ReachableIn entities start euid n)
  (he₁ : .some ed = entities.find? euid)
  (he₂ : .some tv = ed.tags.find? tag)
  (he₃ : EuidInValue tv path euid') :
  ReachableIn entities start euid' (1 + n)
:= by
  cases hr
  case in_start n' hi =>
    have he₄ : euid' ∈ ed.sliceEUIDs := by
      simp [EntityData.sliceEUIDs]
      rw [Set.mem_union_iff_mem_or]
      right
      rw [set_mem_flatten_union_iff_mem_any]
      exists tv.sliceEUIDs
      constructor
      case left =>
        symm at he₂
        exact List.mem_map_of_mem _ (map_find_then_value he₂)
      case right =>
        exact in_val_then_val_slice he₃
    have hr' : ReachableIn entities ed.sliceEUIDs euid' (1 + n') := by
      have hn : 1 + n' = Nat.succ n' := by omega
      rw [hn]
      exact ReachableIn.in_start he₄
    exact ReachableIn.step euid hi he₁ hr'
  case step n' ed' euid'' he₁' hi hr' =>
    have ih := reachable_tag_step hr' he₁ he₂ he₃
    exact ReachableIn.step euid'' hi he₁' ih

theorem reachable_attr_step {n : Nat} {euid euid' : EntityUID} {start : Set EntityUID} {entities : Entities} {ed : EntityData} {path : List Attr}
  (hr : ReachableIn entities start euid n)
  (he₁: .some ed = entities.find? euid)
  (he₂ : EuidInValue (.record ed.attrs) path euid' ) :
  ReachableIn entities start euid' (1 + n)
:= by
  cases hr
  case in_start n' hi =>
    have he₄ : euid' ∈ ed.sliceEUIDs := by
      simp [EntityData.sliceEUIDs]
      rw [Set.mem_union_iff_mem_or]
      left
      rw [set_mem_flatten_union_iff_mem_any]
      cases he₂
      rename_i v a path ha hv
      exists v.sliceEUIDs
      constructor
      case left =>
        exact List.mem_map_of_mem _ (map_find_then_value ha)
      case right =>
        exact in_val_then_val_slice hv
    have hr' : ReachableIn entities ed.sliceEUIDs euid' (1 + n') := by
      have hn : 1 + n' = Nat.succ n' := by omega
      rw [hn]
      exact ReachableIn.in_start he₄
    exact ReachableIn.step euid hi he₁ hr'
  case step n' ed' euid'' he₁' hi hr' =>
    have ih := reachable_attr_step hr' he₁ he₂
    exact ReachableIn.step euid'' hi he₁' ih

theorem slice_at_succ_n_reachable {e : Expr} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {entities : Entities} {path : List Attr}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : checkLevel tx n = LevelCheckResult.mk true true)
  (he : evaluate e request entities = .ok v)
  (ha : EuidInValue v path euid )
  (hf : entities.contains euid) :
  ReachableIn entities request.sliceEUIDs euid (1 + n)
:= by
  cases e
  case lit p =>
    simp [evaluate] at he
    cases p
    case entityUID =>
      simp [typeOf, typeOfLit] at ht
      split at ht <;> simp [ok, err] at ht
      simp [←ht, checkLevel] at hl

    all_goals {
      have ha' := euid_not_in_not_entity_or_record v (by simp [←he])
      simp [ha'] at ha
    }

  case var v =>
    cases v <;> simp [evaluate] at he
    case context =>
      subst he
      have hi : euid ∈ request.sliceEUIDs := by
        rw [Request.sliceEUIDs, Set.mem_union_iff_mem_or, ←Set.make_mem]
        right
        simp [Value.sliceEUIDs]
        cases ha
        rename_i v a path hf' hv
        have ha' := in_val_then_val_slice hv
        rw [set_mem_flatten_union_iff_mem_any]
        exists v.sliceEUIDs
        simp [ha']
        exists a, v
        simp
        exact Map.find?_mem_toList hf'
      have hn : (1 + n) = Nat.succ n := by omega
      rw [hn]
      exact ReachableIn.in_start hi

    all_goals {
      subst he
      have hi : euid ∈ request.sliceEUIDs := by
        rw [Request.sliceEUIDs, Set.mem_union_iff_mem_or, ←Set.make_mem]
        cases ha
        simp [hf]
      have hn : (1 + n) = Nat.succ n := by omega
      rw [hn]
      exact ReachableIn.in_start hi
    }

  case getAttr e a =>
    simp [evaluate] at he
    cases h₁ : evaluate e request entities <;> simp [h₁] at he
    have ⟨ hc', tx', c₁', ht', htx, h₂ ⟩ := type_of_getAttr_inversion ht
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

      have ih := slice_at_succ_n_reachable hc hr ht' hl' h₁ (EuidInValue.euid euid') hf'
      have h₆ : (1 + (n - 1)) = n := by omega
      rw [h₆] at ih ; clear h₆

      have ha' : EuidInValue (Value.record ed.attrs) (a :: path) euid := EuidInValue.record hv ha
      symm at hed
      apply reachable_attr_step ih hed ha'

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
        have ha' : EuidInValue (Value.record attrs) (a :: path) euid := EuidInValue.record hv ha
        exact slice_at_succ_n_reachable hc hr ht' hl h₁ ha' hf

  case hasAttr e a =>
    simp [evaluate] at he
    cases h₁ : evaluate e request entities <;> simp [h₁] at he
    simp [hasAttr] at he
    rename_i v₁
    cases h₂ : attrsOf v₁ λ uid => Except.ok (entities.attrsOrEmpty uid) <;> simp [h₂] at he
    have ha' := euid_not_in_not_entity_or_record v (by simp [←he])
    simp [ha'] at ha

  case ite e₁ e₂ e₃ =>
    have ⟨tx₁, bty₁, c₁, tx₂, c₂, tx₃, c₃, htx, htx₁, hty₁, hif ⟩ := type_of_ite_inversion ht
    have ⟨ hgc, v, he₁, hi₁⟩ := type_of_is_sound hc hr htx₁

    rw [htx] at hl
    simp only [checkLevel, LevelCheckResult.mk.injEq, Bool.and_eq_true] at hl

    simp [evaluate] at he
    cases he₂ : Result.as Bool (evaluate e₁ request entities) <;> simp [he₂] at he
    simp [Result.as, Coe.coe, Value.asBool] at he₂
    split at he₂ <;> try contradiction
    split at he₂ <;> try contradiction
    injections he₂
    subst he₂
    rename_i v₁ b he₂

    split at he
    case isTrue hb =>
      subst hb
      have hl₂ : checkLevel tx₂ n = LevelCheckResult.mk true true := by
        have h : ∀ r, r = LevelCheckResult.mk r.checked r.root := by simp
        rw [h (checkLevel tx₂ n)]
        simp [hl]
      have htx₂ : typeOf e₂ (c ∪ c₁) env = .ok (tx₂, c₂) := by
        split at hif <;> try simp [hif]
        rw [hty₁] at hi₁
        have := instance_of_ff_is_false hi₁
        subst v
        unfold EvaluatesTo at he₁
        simp [he₂] at he₁

      replace hgc : CapabilitiesInvariant c₁ request entities := by
        simp only [he₂, GuardedCapabilitiesInvariant, forall_const] at hgc
        exact hgc
      exact slice_at_succ_n_reachable (capability_union_invariant hc hgc) hr htx₂ hl₂ he ha hf
    case isFalse hb =>
      cases b <;> simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false] at hb ; clear hb
      have hl₃ : checkLevel tx₃ n = LevelCheckResult.mk true true := by
        have h : ∀ r, r = LevelCheckResult.mk r.checked r.root := by simp
        rw [h (checkLevel tx₃ n)]
        simp [hl]
      have htx₃ : typeOf e₃ c env = .ok (tx₃, c₃) := by
        split at hif <;> try simp [hif]
        rw [hty₁] at hi₁
        have := instance_of_tt_is_true hi₁
        subst v
        unfold EvaluatesTo at he₁
        simp [he₂] at he₁
      exact slice_at_succ_n_reachable hc hr htx₃ hl₃ he ha hf

  case and e₁ e₂ | or e₁ e₂ =>
    simp [evaluate] at he
    cases h₁ :  Result.as Bool (evaluate e₁ request entities) <;> simp [h₁] at he
    split at he
    · simp at he
      have ha' := euid_not_in_not_entity_or_record v (by simp [←he])
      simp [ha'] at ha
    · cases h₂ : Result.as Bool (evaluate e₂ request entities) <;> simp [h₂] at he
      have ha' := euid_not_in_not_entity_or_record v (by simp [←he])
      simp [ha'] at ha

  case unaryApp op e =>
    simp [evaluate] at he
    cases he₁ : evaluate e request entities <;> simp [he₁] at he
    simp [apply₁, intOrErr] at he
    (split at he <;> try split at he) <;>
    try simp at he
    all_goals {
      have ha' := euid_not_in_not_entity_or_record v (by simp [←he])
      simp [ha'] at ha
    }

  case binaryApp op e₁ e₂ =>
    simp [evaluate] at he
    cases he₁ : evaluate e₁ request entities <;> simp [he₁] at he
    cases he₂ : evaluate e₂ request entities <;> simp [he₂] at he
    simp [apply₂, intOrErr, hasTag, getTag, inₛ] at he

    (split at he <;> try split at he) <;>
    try simp at he

    case h_13 euid' tag =>
      have ⟨hc', ety, ty, tx₁, tx₂, c₁', c₂', htx₁, hty₁, htx₂, hty₂, ht, htx, hc₁⟩ := type_of_getTag_inversion ht
      subst htx hc'
      have ⟨ hgc₁, v₁, he₁', hi₁ ⟩ := type_of_is_sound hc hr htx₁
      have ⟨ hgc₂, v₂, he₂', hi₂ ⟩ := type_of_is_sound hc hr htx₂
      rename_i hety
      simp [checkLevel] at hl
      have ⟨⟨⟨⟨hl₀, hn⟩, hl₁⟩, hl₂⟩, hl₃⟩ := hl ; clear hl

      replace hl₀ : checkLevel tx₁ (n - 1) = LevelCheckResult.mk true true := by
        have h : ∀ r, r = LevelCheckResult.mk r.checked r.root := by simp
        rw [h (checkLevel tx₁ (n - 1))]
        simp [hl₀, hl₁]

      rw [hty₁] at hi₁

      have ⟨ euid', hety, hv⟩ := instance_of_entity_type_is_entity hi₁
      subst hety hv
      unfold EvaluatesTo at he₁'
      rw [he₁] at he₁'
      cases he₁' <;> rename_i he₁' <;> simp at he₁'
      subst he₁'

      cases he₃ : entities.tags euid' <;> simp [he₃] at he
      rename_i tags
      simp [Map.findOrErr] at he
      split at he <;> simp at he
      subst he
      rename_i v hv

      have ⟨ ed, hed, hed' ⟩ := entities_tags_then_find? he₃
      subst tags
      have hf' : entities.contains euid' := by simp [Map.contains, Option.isSome, hed]

      have ih := slice_at_succ_n_reachable hc hr htx₁ hl₀ he₁ (EuidInValue.euid euid') hf'
      have h₆ : (1 + (n - 1)) = n := by omega
      rw [h₆] at ih ; clear h₆

      symm at hv hed
      apply reachable_tag_step ih hed hv ha

    case h_11 vs =>
      cases he₃ : Set.mapOrErr Value.asEntityUID vs Error.typeError <;> simp [he₃] at he
      have ha' := euid_not_in_not_entity_or_record v (by simp [←he])
      simp [ha'] at ha
    all_goals {
      have ha' := euid_not_in_not_entity_or_record v (by simp [←he])
      simp [ha'] at ha
    }

  case set es =>
    simp [evaluate] at he
    cases he₁ : (es.mapM₁ (λ x => evaluate x.val request entities)) <;> simp [he₁] at he
    have ha' := euid_not_in_not_entity_or_record v (by simp [←he])
    simp [ha'] at ha

  case record attrs =>
    replace ⟨ hc', rty, htx, hfat ⟩  := type_of_record_inversion ht
    subst hc'
    -- unfold AttrExprHasAttrType at hat

    simp [evaluate] at he
    cases he₁ : attrs.mapM₂ λ x => bindAttr x.1.fst (evaluate x.1.snd request entities) <;> simp [he₁] at he
    subst v
    rename_i attrs'
    cases ha
    rename_i v a path hf' hv

    have ⟨ e, he ⟩ : ∃ e, (Map.make attrs).find? a = some e := by
      -- We know `attrs` evals to `attrs'` by `he₁`, and `attr'` contains `a` by
      -- `hv`, so `attrs` must also contain `a`
      sorry
    have he' : evaluate e request entities = Except.ok v := by
      -- From `hv`, `attrs'` contains `v` for attribute `a`. `e` is the
      -- expression for attribute `a` from `he`. `attrs'` contains evaluated
      -- attributes by `he₁`.
      sorry
    have ⟨ t', ht' ⟩ : ∃ t, (Map.make rty).find? a = some t := by
      -- We know `attrs` has type `rty` by `hfat`, and `attrs` contains `a` by
      -- `he`, so `rty` must also contain `a`
      sorry
    have het : AttrExprHasAttrType c env (a, e) (a, t')  := by
      -- We know `a ∈ attrs` and `a ∈ rty` from `ht` and `he`. From `hfat` we
      -- know `e` must then have type `t`.
      sorry
    unfold AttrExprHasAttrType at het
    simp at het
    have ⟨ty', het₁, ⟨ c', het₂ ⟩⟩ := het ; clear het
    subst het₁

    have ⟨ tx', htx', htx'' ⟩ : ∃ tx', typeOf e c env = .ok (tx', c') ∧ tx'.typeOf = ty' :=
      -- `(typeOf e c env).typeOf` is `ok` by `het₂`, so it must also have a
      -- `typeOf e c env` must also be `ok`.
      sorry

    have hl' : checkLevel tx' n = LevelCheckResult.mk true true :=
      -- `tx'` is the result of annotating `e` (by `htx'`), `e` is an attribute
      -- of `attrs` (by `he`), `attrs` annotates to `tx` by `ht`, and `tx` level
      -- checks at `n` by `hl`, so `tx'` must also level check at `n`.
      by sorry

    -- TODO: This proves the goal, but the termination checker isn't happy
    -- exact slice_at_succ_n_reachable hc hr htx' hl' he' (by exists path') hf
    sorry

  case call xfn args =>
    simp only [evaluate] at he
    cases he₁ : args.mapM₁ fun x => evaluate x.val request entities <;>
    simp only [he₁, Except.bind_err, reduceCtorEq] at he

    simp only [call, res, Except.bind_ok] at he
    (split at he <;> try split at he) <;>
    simp only [Except.ok.injEq, reduceCtorEq] at he

    all_goals {
      have ha' := euid_not_in_not_entity_or_record v (by simp [←he])
      simp [ha'] at ha
    }

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
  cases h₂ : (List.mapM (λ e => (Map.find? entities e).bind λ ed => some (e, ed)) eids.elts)  <;> simp [h₂] at hs
  subst hs
  have hf' : Map.contains entities euid := by simp [Map.contains, hf]
  have hw : ReachableIn entities request.sliceEUIDs euid (1 + n) := slice_at_succ_n_reachable hc hr ht hl he (EuidInValue.euid euid) hf'
  symm at h₁
  have hi := slice_contains_reachable hw h₁ (by simp [hf, Map.contains_iff_some_find?])
  rw [←hf]
  symm at h₂
  exact map_find_mapm_value h₂ hi

theorem slice_at_zero_empty_inner
  (hs : Entities.sliceAtLevel.sliceAtLevel entities work 0 = some slice)
  : slice = ∅
:= by
  simp only [Entities.sliceAtLevel.sliceAtLevel, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hs
  symm at hs
  exact hs

theorem slice_at_zero_empty {request : Request} {entities slice : Entities}
  (hs : some slice = Entities.sliceAtLevel entities request 0)
  : slice = Map.empty
:= by
  unfold Entities.sliceAtLevel at hs
  cases h₁ : Entities.sliceAtLevel.sliceAtLevel entities request.sliceEUIDs 0 <;> simp [h₁] at hs
  replace h₁ := slice_at_zero_empty_inner h₁
  simp only [h₁, Set.elts, Set.instEmptyCollection, Set.empty, List.mapM_nil, Option.pure_def, Option.some_bind, Option.some.injEq] at hs
  exact hs
