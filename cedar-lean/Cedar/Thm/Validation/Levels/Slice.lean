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

import Cedar.Thm.Validation.Levels.Data

namespace Cedar.Thm

/-!
This file contains the main lemma describing the behavior of slicing `checked_eval_entity_in_slice`
-/

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

theorem entities_tags_then_find? {entities: Entities} {tags : Map Tag Value} {uid : EntityUID}
  (he : entities.tags uid = .ok tags)
  : ∃ ed, entities.find? uid = some ed ∧ ed.tags = tags
:= by sorry

theorem entities_find?_then_tags {entities: Entities} {ed : EntityData} {uid : EntityUID}
  (he : entities.find? uid = some ed)
  : .ok ed.tags = entities.tags uid
:= by sorry

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
  · rename_i level
    cases hs₁ : (List.mapM (Map.find? entities) work.elts) <;> simp [hs₁] at hs
    rename_i eds
    cases hs₂ : (List.mapM (λ x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs level) eds) <;> simp [hs₂] at hs
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
  (he : entities.attrs uid = .error e)
  : slice.attrs uid = .error e
:= by
  simp only [Entities.attrs, Map.findOrErr] at he
  split at he <;> simp at he
  rename_i hf
  cases hf₁ : entities.find? uid <;> simp only [hf₁, Option.some.injEq, forall_eq'] at hf
  simp [he, not_entities_then_not_slice hs hf₁, Entities.attrs, Map.findOrErr]

inductive ReachableIn : Entities → Set EntityUID → EntityUID → Nat → Prop where
  | in_start {es : Entities} {start : Set EntityUID} {finish : EntityUID} {level : Nat}
    (hs : finish ∈ start) :
    ReachableIn es start finish level.succ
  | step {es : Entities} {start : Set EntityUID} {finish : EntityUID} {level : Nat} {ed : EntityData}
    (i : EntityUID)
    (hi : i ∈ start)
    (he : es.find? i = some ed)
    (hr : ReachableIn es ed.sliceEUIDs finish level) :
    ReachableIn es start finish level.succ

inductive EuidInValue : Value → List Attr → EntityUID → Prop where
  | euid (euid : EntityUID) :
    EuidInValue (.prim (.entityUID euid)) [] euid
  | record {a : Attr} {path : List Attr} {attrs : Map Attr Value}
    (ha : attrs.find? a = some v)
    (hv : EuidInValue v path euid) :
    EuidInValue (.record attrs)  (a :: path) euid

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
    simp only [Value.sliceEUIDs]
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
  (he₁ : entities.find? euid = some ed)
  (he₂ : ed.tags.find? tag = some tv)
  (he₃ : EuidInValue tv path euid') :
  ReachableIn entities start euid' n.succ
:= by
  cases hr
  case in_start n' hi =>
    have he₄ : euid' ∈ ed.sliceEUIDs := by
      simp only [EntityData.sliceEUIDs]
      rw [Set.mem_union_iff_mem_or]
      right
      rw [set_mem_flatten_union_iff_mem_any]
      exists tv.sliceEUIDs
      constructor
      case left =>
        exact List.mem_map_of_mem _ (map_find_then_value he₂)
      case right =>
        exact in_val_then_val_slice he₃
    have hr' : ReachableIn entities ed.sliceEUIDs euid' n'.succ :=
      ReachableIn.in_start he₄
    exact ReachableIn.step euid hi he₁ hr'
  case step n' ed' euid'' he₁' hi hr' =>
    have ih := reachable_tag_step hr' he₁ he₂ he₃
    exact ReachableIn.step euid'' hi he₁' ih

theorem reachable_attr_step {n : Nat} {euid euid' : EntityUID} {start : Set EntityUID} {entities : Entities} {ed : EntityData} {path : List Attr}
  (hr : ReachableIn entities start euid n)
  (he₁: entities.find? euid = some ed)
  (he₂ : EuidInValue (.record ed.attrs) path euid' ) :
  ReachableIn entities start euid' n.succ
:= by
  cases hr
  case in_start n' hi =>
    have he₄ : euid' ∈ ed.sliceEUIDs := by
      simp only [EntityData.sliceEUIDs]
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
    have hr' : ReachableIn entities ed.sliceEUIDs euid' n'.succ :=
      ReachableIn.in_start he₄
    exact ReachableIn.step euid hi he₁ hr'
  case step n' ed' euid'' he₁' hi hr' =>
    have ih := reachable_attr_step hr' he₁ he₂
    exact ReachableIn.step euid'' hi he₁' ih

/--
If an expression checks at level `n` and then evaluates an entity (or a record
containing an entity), then that entity must reachable in `n + 1` steps.
-/
theorem checked_eval_entity_reachable {e : Expr} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {entities : Entities} {path : List Attr}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : checkLevel tx n = LevelCheckResult.mk true true)
  (he : evaluate e request entities = .ok v)
  (ha : EuidInValue v path euid )
  (hf : entities.contains euid) :
  ReachableIn entities request.sliceEUIDs euid n.succ
:= by
  cases e
  case lit p =>
    simp only [evaluate, Except.ok.injEq] at he
    cases p
    case entityUID =>
      subst v ; cases ha
      replace ht : tx = TypedExpr.lit (Prim.entityUID euid) (CedarType.entity euid.ty) := by
        simp only [typeOf, typeOfLit, Function.comp_apply] at ht
        split at ht <;> simp only [ok, err, reduceCtorEq, Except.ok.injEq, Prod.mk.injEq] at ht
        simp [ht]
      simp [ht, checkLevel] at hl
    all_goals { subst he ; cases ha }

  case var v =>
    cases v <;> simp only [evaluate, Except.ok.injEq] at he
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
      exact ReachableIn.in_start hi

    all_goals {
      subst he
      have hi : euid ∈ request.sliceEUIDs := by
        rw [Request.sliceEUIDs, Set.mem_union_iff_mem_or, ←Set.make_mem]
        cases ha
        simp [hf]
      exact ReachableIn.in_start hi
    }

  case getAttr e a =>
    simp [evaluate] at he
    cases he₁ : evaluate e request entities <;> simp [he₁] at he
    have ⟨ hc', tx', c₁', ht', htx, h₂ ⟩ := type_of_getAttr_inversion ht
    rw [htx] at hl
    simp only [checkLevel, gt_iff_lt] at hl
    have ⟨ hgc, v, he', hi ⟩ := type_of_is_sound hc hr ht'
    split at hl
    · rename_i hety
      rw [hety] at hi
      have ⟨ euid', hety, hv⟩  := instance_of_entity_type_is_entity hi
      subst hety hv
      unfold EvaluatesTo at he'
      rw [he₁] at he'
      cases he' <;> rename_i he' <;> simp at he'
      subst he'

      simp [getAttr, attrsOf] at he
      cases he₂ : entities.attrs euid' <;> simp [he₂] at he
      rename_i attrs
      simp [Map.findOrErr] at he
      split at he <;> simp at he
      subst he
      rename_i v hv

      simp only [LevelCheckResult.mk.injEq, Bool.and_eq_true, decide_eq_true_eq] at hl
      have hl' : checkLevel tx' (n - 1) = LevelCheckResult.mk true true := by
        have h : ∀ r, r = LevelCheckResult.mk r.checked r.root := by simp
        rw [h (checkLevel tx' (n - 1))]
        simp [hl]

      have ⟨ ed, hed, hed' ⟩ := entities_attrs_then_find? he₂
      subst attrs
      have hf' : entities.contains euid' := by simp [Map.contains, Option.isSome, hed]

      have ih := checked_eval_entity_reachable hc hr ht' hl' he₁ (EuidInValue.euid euid') hf'

      have hn : (n - 1).succ = n := by
        have _ : 0 < n := by simp [hl]
        omega
      rw [hn] at ih ; clear hn

      have ha' : EuidInValue (Value.record ed.attrs) (a :: path) euid := EuidInValue.record hv ha
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
        rw [he₁] at he'
        cases he' <;> rename_i he' <;> simp at he'
        subst he'
        simp [getAttr, attrsOf, Map.findOrErr] at he
        split at he <;> simp at he
        rename_i v hv
        subst he
        have ha' : EuidInValue (Value.record attrs) (a :: path) euid := EuidInValue.record hv ha
        exact checked_eval_entity_reachable hc hr ht' hl he₁ ha' hf

  case hasAttr e a =>
    simp [evaluate] at he
    cases he₁ : evaluate e request entities <;> simp [he₁] at he
    simp [hasAttr] at he
    rename_i v₁
    cases he₂ : attrsOf v₁ λ uid => Except.ok (entities.attrsOrEmpty uid) <;> simp [he₂] at he
    subst he ; cases ha

  case ite e₁ e₂ e₃ =>
    have ⟨tx₁, bty₁, c₁, tx₂, c₂, tx₃, c₃, htx, htx₁, hty₁, hif ⟩ := type_of_ite_inversion ht
    have ⟨ hgc, v, he₁, hi₁⟩ := type_of_is_sound hc hr htx₁

    rw [htx] at hl
    simp only [checkLevel, LevelCheckResult.mk.injEq, Bool.and_eq_true] at hl

    simp [evaluate] at he
    cases he₁ : Result.as Bool (evaluate e₁ request entities) <;> simp [he₁] at he
    simp [Result.as, Coe.coe, Value.asBool] at he₁
    split at he₁ <;> try contradiction
    split at he₁ <;> try contradiction
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
      exact checked_eval_entity_reachable (capability_union_invariant hc hgc) hr htx₂ hl₂ he ha hf
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
      exact checked_eval_entity_reachable hc hr htx₃ hl₃ he ha hf

  case and e₁ e₂ | or e₁ e₂ =>
    simp [evaluate] at he
    cases he₁ :  Result.as Bool (evaluate e₁ request entities) <;> simp [he₁] at he
    split at he
    · simp at he
      subst he ; cases ha
    · cases he₂ : Result.as Bool (evaluate e₂ request entities) <;> simp [he₂] at he
      subst he ; cases ha

  case unaryApp op e =>
    simp [evaluate] at he
    cases he₁ : evaluate e request entities <;> simp [he₁] at he
    simp [apply₁, intOrErr] at he
    (split at he <;> try split at he) <;>
    try simp at he
    all_goals { subst he ; cases ha }

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

      have ih := checked_eval_entity_reachable hc hr htx₁ hl₀ he₁ (EuidInValue.euid euid') hf'
      have h₆ : (n - 1).succ = n := by omega
      rw [h₆] at ih ; clear h₆
      apply reachable_tag_step ih hed hv ha

    case h_11 vs =>
      cases he₃ : Set.mapOrErr Value.asEntityUID vs Error.typeError <;> simp [he₃] at he
      subst he ; cases ha
    all_goals { subst he ; cases ha }

  case set es =>
    simp [evaluate] at he
    cases he₁ : (es.mapM₁ (λ x => evaluate x.val request entities)) <;> simp [he₁] at he
    subst he ; cases ha

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
    -- exact checked_eval_entity_reachable hc hr htx' hl' he' (by exists path') hf
    sorry

  case call xfn args =>
    simp only [evaluate] at he
    cases he₁ : args.mapM₁ fun x => evaluate x.val request entities <;>
      simp only [he₁, Except.bind_err, reduceCtorEq] at he

    simp only [call, res, Except.bind_ok] at he
    (split at he <;> try split at he) <;>
    simp only [Except.ok.injEq, reduceCtorEq] at he

    all_goals { subst he ; cases ha }

theorem in_work_then_in_slice {entities : Entities} {work slice : Set EntityUID} {euid : EntityUID} {n : Nat}
  (hw : euid ∈ work)
  (hs : Entities.sliceAtLevel.sliceAtLevel entities work n.succ = some slice)
  : euid ∈ slice
:= by
  unfold Entities.sliceAtLevel.sliceAtLevel at hs
  cases hs₁ :
    List.mapM (Map.find? entities) work.elts
  <;> simp [hs₁] at hs
  rename_i eds
  cases hs₂ :
    List.mapM (λ x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs n) eds
  <;> simp [hs₂] at hs
  rename_i slice'
  subst hs
  have ⟨ _, hc ⟩ := Set.mem_union_iff_mem_or work (flatten_union slice') euid
  apply hc
  simp [hw]

/--
If an entity is reachable in `n` steps, then it must be included in slice at
`n`. This lemma talks about the inner slicing function, so it's possible that
the entity isn't in the original entities if it's in `work`.
-/
theorem slice_contains_reachable {n: Nat} {work : Set EntityUID} {euid : EntityUID} {entities : Entities} {slice : Set EntityUID}
  (hw : ReachableIn entities work euid n.succ)
  (hs : Entities.sliceAtLevel.sliceAtLevel entities work n.succ = some slice) :
  euid ∈ slice
:= by
  cases hw
  case in_start hw =>
    exact in_work_then_in_slice hw hs
  case step ed euid' hf hi hw =>
    unfold Entities.sliceAtLevel.sliceAtLevel at hs
    cases hs₁ : (List.mapM (Map.find? entities) work.elts) <;>
      simp only [hs₁, Option.bind_none_fun, reduceCtorEq] at hs
    rename_i eds
    cases hs₂ : Option.map flatten_union (List.mapM (λ x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs n) eds) <;>
      simp only [hs₂, Option.map_eq_map, Option.bind_eq_bind, Option.bind_some_fun, Option.none_bind, reduceCtorEq, Option.some_bind, Option.some.injEq] at hs
    subst hs
    rename_i slice'
    cases hs₃ : List.mapM (λ x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs n) eds <;>
      simp only [hs₃, Option.map_some', Option.some.injEq, Option.map_none', reduceCtorEq] at hs₂
    subst hs₂
    rw [Set.mem_union_iff_mem_or]
    right
    have ⟨ ed, hi₁, hf₁ ⟩ := List.mapM_some_implies_all_some hs₁ _ hi
    have ⟨ slice, _, hs ⟩ := List.mapM_some_implies_all_some hs₃ _ hi₁
    rw [hf₁] at hf ; injections hf ; subst hf
    cases hs₄ : Entities.sliceAtLevel.sliceAtLevel entities ed.sliceEUIDs n <;>
      simp only [hs₄, reduceCtorEq, Option.some.injEq] at hs
    cases n
    case zero => cases hw
    case succ n =>
      have ih := slice_contains_reachable hw hs₄
      rw [set_mem_flatten_union_iff_mem_any]
      subst hs
      rename_i ed_slice _
      exists ed_slice

/--
If an expression checks at level `n` and then evaluates to an entity, then that
entity must be in a slice at `n + 1`.
-/
theorem checked_eval_entity_in_slice  {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {slice entities : Entities} {ed : EntityData}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : checkLevel tx n = LevelCheckResult.mk true true)
  (he : evaluate e request entities = .ok (Value.prim (Prim.entityUID euid)))
  (hf : entities.find? euid = some ed)
  (hs : slice = Entities.sliceAtLevel entities request n.succ) :
  slice.find? euid = some ed
:= by
  simp only [Entities.sliceAtLevel] at hs
  cases hs₁ : Entities.sliceAtLevel.sliceAtLevel entities request.sliceEUIDs n.succ  <;>
    simp only [hs₁, Option.bind_none_fun, reduceCtorEq] at hs
  rename_i eids
  cases hs₂ : (List.mapM (λ e => (Map.find? entities e).bind λ ed => some (e, ed)) eids.elts) <;>
    simp only [hs₂, Option.bind_eq_bind, Option.bind_some_fun, Option.none_bind, reduceCtorEq, Option.some_bind, Option.some.injEq] at hs
  subst hs
  have hf₁ : Map.contains entities euid := by simp [Map.contains, hf]
  have hw : ReachableIn entities request.sliceEUIDs euid n.succ :=
    checked_eval_entity_reachable hc hr ht hl he (EuidInValue.euid euid) hf₁
  have hi := slice_contains_reachable hw hs₁
  rw [←hf]
  exact map_find_mapm_value hs₂ hi
