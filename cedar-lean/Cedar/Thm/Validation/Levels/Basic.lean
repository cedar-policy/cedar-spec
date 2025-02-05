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

theorem not_entities_then_not_slice_attrs_inner {n: Nat}  {uid : EntityUID} {e : Error} {entities : Entities} {work slice : Set EntityUID}
  (hs : some slice = Entities.sliceAtLevel.sliceAtLevel entities work n)
  (hne : uid ∉ entities)
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

theorem not_entities_attrs_then_not_slice_attrs {n: Nat} {request : Request} {uid : EntityUID} {e : Error} {entities slice : Entities}
  (hs : slice = Entities.sliceAtLevel entities request n)
  (hse : entities.attrs uid = .error e)
  : slice.attrs uid = .error e
:= by sorry

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
      cases h₈ : Option.map flatten_union (List.mapM (λ x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs (1 + (n' + 1) - 1)) eds) <;> simp [h₈] at hs
      subst hs
      rename_i slice'
      cases h₉ : List.mapM (λ x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs (1 + (n' + 1) - 1)) eds <;> simp [h₉] at h₈
      subst h₈
      rw [Set.mem_union_iff_mem_or]
      right
      have ⟨ e', h₁₀, h₁₁⟩ := List.mapM_some_implies_all_some h₇ _ hi
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
    rw [set_mem_flatten_union_iff_mem_any]
    exists v.sliceEUIDs
    simp only [ih, List.mem_map, Subtype.exists, Prod.exists, and_true]
    exists a, v
    simp [Map.find?_mem_toList, ha]
  case set | ext =>
    unfold EuidInValue at hv
    split at hv <;> split at hv <;>
    ( rename_i hv' ; simp at hv hv' )

theorem reachable_attr_step {n : Nat} {euid euid' : EntityUID} {start : Set EntityUID} {entities : Entities} {ed : EntityData}
  (hr : ReachableIn entities start euid n)
  (he₁: .some ed = entities.find? euid)
  (he₂ : ∃ path, EuidInValue (.record ed.attrs) path euid' ) :
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
      rw [set_mem_flatten_union_iff_mem_any]
      replace ⟨ path, he₂ ⟩ := he₂
      unfold EuidInValue at he₂
      simp at he₂
      split at he₂ <;> try contradiction
      split at he₂ <;> try contradiction
      rename_i path a path' _ v hv
      exists v.sliceEUIDs
      constructor
      ·
        exact List.mem_map_of_mem _ (map_find_then_value hv)
      · exact in_val_then_val_slice he₂
    case inr hr =>
      have ⟨ euid'', hs, ed'', hrl, hrr ⟩ := hr ; clear hr
      right
      exists euid''
      simp only [hs, true_and]
      exists ed''
      simp only [hrl, true_and]
      have hn' : (1 + n - 1) = (1 + (n - 1)) := by simp at hn; omega
      rw [hn']
      exact reachable_attr_step hrr he₁ he₂

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
      rw [set_mem_flatten_union_iff_mem_any]
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
      have ha' : ∃ path, EuidInValue (Value.record ed.attrs) path euid := by
        replace ⟨ path,  ha ⟩ := ha
        exists a :: path
        simp [EuidInValue, ←hv, ha]
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
  cases h₂ : (List.mapM (λ e => (Map.find? entities e).bind λ ed => some (e, ed)) eids.elts)  <;> simp [h₂] at hs
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

--- Don't need this lemma atm.
/--
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
--/

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
