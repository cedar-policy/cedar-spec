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
import Cedar.Thm.Validation.Levels.CheckLevel

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

theorem not_entities_then_not_slice {n: Nat} {request : Request} {uid : EntityUID} {entities slice : Entities}
  (hs : some slice = Entities.sliceAtLevel entities request n)
  (hse : entities.find? uid = none)
  : slice.find? uid = none
:= by
  simp only [Entities.sliceAtLevel] at hs
  cases hs₁ : Entities.sliceAtLevel.sliceAtLevel entities request.sliceEUIDs n <;>
    simp only [hs₁, Option.bind_none_fun, reduceCtorEq] at hs
  rename_i eids
  cases hs₂ : (List.mapM (λ e => (Map.find? entities e).bind λ ed => some (e, ed)) eids.elts) <;>
    simp only [hs₂, Option.bind_eq_bind, Option.bind_some_fun, Option.none_bind, reduceCtorEq, Option.some_bind, Option.some.injEq] at hs
  subst hs
  exact mapm_none_find_none hs₂ hse

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
    ReachableIn es start finish (level + 1)
  | step {es : Entities} {start : Set EntityUID} {finish : EntityUID} {level : Nat} {ed : EntityData}
    (i : EntityUID)
    (hi : i ∈ start)
    (he : es.find? i = some ed)
    (hr : ReachableIn es ed.sliceEUIDs finish level) :
    ReachableIn es start finish (level + 1)

inductive EuidInValue : Value → List Attr → EntityUID → Prop where
  | euid (euid : EntityUID) :
    EuidInValue (.prim (.entityUID euid)) [] euid
  | record {a : Attr} {path : List Attr} {attrs : Map Attr Value}
    (ha : attrs.find? a = some v)
    (hv : EuidInValue v path euid) :
    EuidInValue (.record attrs)  (a :: path) euid

theorem reachable_succ {n : Nat} {euid : EntityUID} {start : Set EntityUID} {entities : Entities}
  (hr : ReachableIn entities start euid n)
  : ReachableIn entities start euid (n + 1)
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
    unfold Value.sliceEUIDs List.attach₃
    simp only [List.map_pmap_subtype (λ e : (Attr × Value) => e.snd.sliceEUIDs) attrs.1]
    rw [set_mem_union_all_iff_mem_any]
    exists v.sliceEUIDs
    simp only [ih, List.mem_map, Subtype.exists, Prod.exists, and_true]
    exists a, v
    replace ha := Map.find?_mem_toList ha
    unfold Map.toList at ha
    simp [ha]
  case set | ext => cases hv

theorem reachable_tag_step {n : Nat} {euid euid' : EntityUID} {start : Set EntityUID} {entities : Entities} {ed : EntityData} {tag : Tag} {path : List Attr}
  (hr : ReachableIn entities start euid n)
  (he₁ : entities.find? euid = some ed)
  (he₂ : ed.tags.find? tag = some tv)
  (he₃ : EuidInValue tv path euid') :
  ReachableIn entities start euid' (n + 1)
:= by
  cases hr
  case in_start n' hi =>
    have he₄ : euid' ∈ ed.sliceEUIDs := by
      simp only [EntityData.sliceEUIDs]
      rw [Set.mem_union_iff_mem_or]
      right
      rw [set_mem_union_all_iff_mem_any]
      exists tv.sliceEUIDs
      constructor
      case left =>
        exact List.mem_map_of_mem _ (map_find_then_value he₂)
      case right =>
        exact in_val_then_val_slice he₃
    have hr' : ReachableIn entities ed.sliceEUIDs euid' (n' + 1) :=
      ReachableIn.in_start he₄
    exact ReachableIn.step euid hi he₁ hr'
  case step n' ed' euid'' he₁' hi hr' =>
    have ih := reachable_tag_step hr' he₁ he₂ he₃
    exact ReachableIn.step euid'' hi he₁' ih

theorem reachable_attr_step {n : Nat} {euid euid' : EntityUID} {start : Set EntityUID} {entities : Entities} {ed : EntityData} {path : List Attr}
  (hr : ReachableIn entities start euid n)
  (he₁: entities.find? euid = some ed)
  (he₂ : EuidInValue (.record ed.attrs) path euid' ) :
  ReachableIn entities start euid' (n + 1)
:= by
  cases hr
  case in_start n' hi =>
    have he₄ : euid' ∈ ed.sliceEUIDs := by
      simp only [EntityData.sliceEUIDs]
      rw [Set.mem_union_iff_mem_or]
      left
      rw [set_mem_union_all_iff_mem_any]
      cases he₂
      rename_i v a path ha hv
      exists v.sliceEUIDs
      constructor
      case left =>
        exact List.mem_map_of_mem _ (map_find_then_value ha)
      case right =>
        exact in_val_then_val_slice hv
    have hr' : ReachableIn entities ed.sliceEUIDs euid' (n' + 1) :=
      ReachableIn.in_start he₄
    exact ReachableIn.step euid hi he₁ hr'
  case step n' ed' euid'' he₁' hi hr' =>
    have ih := reachable_attr_step hr' he₁ he₂
    exact ReachableIn.step euid'' hi he₁' ih

theorem var_entity_reachable {var : Var} {v : Value} {n : Nat} {request : Request} {entities : Entities} {euid : EntityUID} {path : List Attr}
  (he : evaluate (.var var) request entities = .ok v)
  (ha : EuidInValue v path euid)
  (hf : entities.contains euid) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  have hi : euid ∈ request.sliceEUIDs := by
    rw [Request.sliceEUIDs, Set.mem_union_iff_mem_or, ←Set.make_mem]
    cases var <;> simp [evaluate] at he <;> subst he <;> cases ha
    case principal | action | resource => simp [hf]
    case context v a path hf' hv =>
      right
      unfold Value.sliceEUIDs List.attach₃
      simp only [List.map_pmap_subtype (λ e : (Attr × Value) => e.snd.sliceEUIDs) request.4.1]
      simp only [set_mem_union_all_iff_mem_any, List.mem_map, Subtype.exists, Prod.exists]
      exists v.sliceEUIDs
      replace hv := in_val_then_val_slice hv
      simp only [hv, and_true]
      exists a, v
      replace hf' := Map.find?_mem_toList hf'
      unfold Map.toList at hf'
      simp [hf']
  exact ReachableIn.in_start hi

theorem record_value_attr_expr_attr'  {rxs : List (Attr × Expr)}
   (h₁ : (rxs.mapM λ (a, x) => bindAttr a (evaluate x request entities)) = .ok rvs)
   (h₂ : (Map.mk rvs).find? a = some v) :
   ∃ tx, (Map.mk rxs).find? a = some tx ∧ evaluate tx request entities = .ok v
:= by
  cases rvs
  case nil =>
    simp [pure, Except.pure, Map.find?, List.find?] at h₂
  case cons hv tvs =>
    cases rxs
    case nil =>
      simp [pure, Except.pure, Map.find?, List.find?] at h₁
    case cons hx txs  =>
      simp at h₁
      cases h₃ : bindAttr hx.fst (evaluate hx.snd request entities) <;> simp [h₃] at h₁
      sorry

theorem record_value_attr_expr_attr  {rxs : List (Attr × Expr)}
   (h₁ : (rxs.mapM₂ λ ax => bindAttr ax.val.fst (evaluate ax.val.snd request entities)) = Except.ok rvs)
   (h₂ : (Map.make rvs).find? a = some v) :
   ∃ tx, (Map.make rxs).find? a = some tx ∧ evaluate tx request entities = .ok v
:= by
  simp [List.mapM₂, List.attach₂] at h₁
  let f := fun (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd request entities)
  simp [List.mapM_pmap_subtype f] at h₁
  sorry
  -- exact record_value_attr_expr_attr' h₁ h₂
--  cases rvs <;> cases rxs
--  all_goals
--    simp [Map.make, List.canonicalize, Map.find?, List.find?] at h₂
--  case nil =>
--    simp [List.mapM₂,List.attach₂, pure, Except.pure] at h₁
--  rename_i h t
--  split at h₂ <;> simp at h₂
--  subst h₂

/--
If an expression checks at level `n` and then evaluates an entity (or a record
containing an entity), then that entity must reachable in `n + 1` steps.
-/
theorem checked_eval_entity_reachable {e : Expr} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {entities : Entities} {path : List Attr}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : checkLevel tx n)
  (hel : ¬ EntityLit tx path)
  (he : evaluate e request entities = .ok v)
  (ha : EuidInValue v path euid)
  (hf : entities.contains euid) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  cases e
  case lit p =>
    cases p
    case entityUID =>
      replace ⟨ _, ht ⟩ := type_of_lit_inversion ht
      rw [←ht] at hel
      specialize hel (by constructor)
      contradiction
    all_goals {
      simp [evaluate] at he
      subst he
      cases ha
     }
  case var v =>
    exact var_entity_reachable he ha hf

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

      simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
      have ⟨⟨hl₁, _⟩, hl₂ ⟩ := hl
      rw [not_entity_lit_spec] at hl₁

      have ⟨ ed, hed, hed' ⟩ := entities_attrs_then_find? he₂
      subst attrs
      have hf' : entities.contains euid' := by simp [Map.contains, Option.isSome, hed]

      have ih := checked_eval_entity_reachable hc hr ht' hl₂ hl₁ he₁ (EuidInValue.euid euid') hf'

      have hn : ((n - 1) + 1) = n := by
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
        have hrt' : ¬ EntityLit tx' (a :: path) := by
          rw [htx] at hel
          intros hel'
          apply hel
          constructor
          assumption
        exact checked_eval_entity_reachable hc hr ht' hl hrt' he₁ ha' hf

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
    simp only [checkLevel, Bool.and_eq_true] at hl
    have ⟨⟨ hl₁, hl₂⟩, hl₃⟩ := hl

    rw [htx] at hel
    have hel₂ : ¬ EntityLit tx₂ path := by
      intros hel₂
      exact hel (EntityLit.ite_true hel₂)
    have hel₃ : ¬ EntityLit tx₃ path := by
      intros hel₃
      exact hel (EntityLit.ite_false hel₃)

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
      exact checked_eval_entity_reachable (capability_union_invariant hc hgc) hr htx₂ hl₂ hel₂ he ha hf
    case isFalse hb =>
      cases b <;> simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false] at hb ; clear hb
      have htx₃ : typeOf e₃ c env = .ok (tx₃, c₃) := by
        split at hif <;> try simp [hif]
        rw [hty₁] at hi₁
        have := instance_of_tt_is_true hi₁
        subst v
        unfold EvaluatesTo at he₁
        simp [he₂] at he₁
      exact checked_eval_entity_reachable hc hr htx₃ hl₃ hel₃ he ha hf

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
      have ⟨⟨⟨hrt₁, hn⟩, hl₁⟩, hl₂⟩ := hl ; clear hl
      rw [hty₁] at hi₁
      rw [not_entity_lit_spec] at hrt₁

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

      have ih := checked_eval_entity_reachable hc hr htx₁ hl₁ hrt₁ he₁ (EuidInValue.euid euid') hf'
      have h₆ : ((n - 1) + 1) = n := by omega
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

  case record rxs =>
    have ⟨ hc', rtxs, htx, hfat ⟩ := type_of_record_inversion ht
    subst hc' htx

    simp [evaluate] at he
    cases he₁ : rxs.mapM₂ λ x => bindAttr x.1.fst (evaluate x.1.snd request entities) <;> simp [he₁] at he
    subst he
    cases ha
    rename_i rvs v a path' hf' hv

    have ⟨ x, hfx, hex ⟩ : ∃ x, (Map.make rxs).find? a = some x ∧ evaluate x request entities = .ok v := by
      -- Have `he₁ : (rxs.mapM₂ fun x => bindAttr x.val.fst (evaluate x.val.snd request entities)) = Except.ok rvs)`
      -- and `hf' : (Map.make rvs).find? a = some v`
      -- so I should be able to show that `a` is in `rxs` and that the associated expr evaluates to `v`
      sorry

    have ⟨atx, hfatx, het⟩ : ∃ atx, (Map.make rtxs).find? a = some atx ∧ AttrExprHasAttrType c env (a, x) (a, atx)  := by
      have he' := Map.make_mem_list_mem (Map.find?_mem_toList hfx)
      replace hfat' := List.forall₂_implies_all_left hfat
      have ⟨ atx, _, haty ⟩ := hfat' (a, x) he'
      have ⟨_, _, hf'', ht''⟩ := find_make_xs_find_make_txs hfat hfx
      have haty' := haty
      unfold AttrExprHasAttrType at haty'
      have ⟨haty₁, _, haty₂⟩ := haty ; clear haty'
      subst haty₁
      exists atx.snd
      simp [ht''] at haty₂
      simp only [haty]
      simp [←haty₂, ht'', hf'']

    unfold AttrExprHasAttrType at het
    simp only [Prod.mk.injEq, true_and, exists_and_left] at het
    replace ⟨_, het ⟩ := het

    have hl' : checkLevel atx n = true := by
      rw [←level_spec] at hl ⊢
      cases hl
      rename_i hl
      specialize hl (a, atx) (Map.make_mem_list_mem (Map.find?_mem_toList hfatx))
      simp [hl]

    have hel' : ¬ EntityLit atx path' := by
      intro hel'
      apply hel
      exact EntityLit.record hfatx hel'

    have : sizeOf x < sizeOf (Expr.record rxs) := by
      replace he := Map.make_mem_list_mem (Map.find?_mem_toList hfx)
      have h₁ := List.sizeOf_lt_of_mem he
      rw [Prod.mk.sizeOf_spec a x] at h₁
      simp
      omega
    exact checked_eval_entity_reachable hc hr het hl' hel' hex hv hf

  case call xfn args =>
    simp only [evaluate] at he
    cases he₁ : args.mapM₁ fun x => evaluate x.val request entities <;>
      simp only [he₁, Except.bind_err, reduceCtorEq] at he

    simp only [call, res, Except.bind_ok] at he
    (split at he <;> try split at he) <;>
    simp only [Except.ok.injEq, reduceCtorEq] at he

    all_goals { subst he ; cases ha }
termination_by e

theorem in_work_then_in_slice {entities : Entities} {work slice : Set EntityUID} {euid : EntityUID} {n : Nat}
  (hw : euid ∈ work)
  (hs : Entities.sliceAtLevel.sliceAtLevel entities work (n + 1) = some slice)
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
  have ⟨ _, hc ⟩ := Set.mem_union_iff_mem_or work slice'.unionAll euid
  apply hc
  simp [hw]

/--
If an entity is reachable in `n` steps, then it must be included in slice at
`n`. This lemma talks about the inner slicing function, so it's possible that
the entity isn't in the original entities if it's in `work`.
-/
theorem slice_contains_reachable {n: Nat} {work : Set EntityUID} {euid : EntityUID} {entities : Entities} {slice : Set EntityUID}
  (hw : ReachableIn entities work euid (n + 1))
  (hs : Entities.sliceAtLevel.sliceAtLevel entities work (n + 1) = some slice) :
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
    cases hs₂ : Option.map List.unionAll (List.mapM (λ x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs n) eds) <;>
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
    match n with
    | 0 => cases hw
    | n + 1 =>
      have ih := slice_contains_reachable hw hs₄
      rw [set_mem_union_all_iff_mem_any]
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
  (hl : checkLevel tx n)
  (hrt : notEntityLit tx)
  (he : evaluate e request entities = .ok (Value.prim (Prim.entityUID euid)))
  (hf : entities.find? euid = some ed)
  (hs : slice = Entities.sliceAtLevel entities request (n + 1)) :
  slice.find? euid = some ed
:= by
  simp only [Entities.sliceAtLevel] at hs
  cases hs₁ : Entities.sliceAtLevel.sliceAtLevel entities request.sliceEUIDs (n + 1)  <;>
    simp only [hs₁, Option.bind_none_fun, reduceCtorEq] at hs
  rename_i eids
  cases hs₂ : (List.mapM (λ e => (Map.find? entities e).bind λ ed => some (e, ed)) eids.elts) <;>
    simp only [hs₂, Option.bind_eq_bind, Option.bind_some_fun, Option.none_bind, reduceCtorEq, Option.some_bind, Option.some.injEq] at hs
  subst hs
  have hf₁ : Map.contains entities euid := by simp [Map.contains, hf]
  rewrite [not_entity_lit_spec] at hrt
  have hw : ReachableIn entities request.sliceEUIDs euid (n + 1) :=
    checked_eval_entity_reachable hc hr ht hl hrt he (EuidInValue.euid euid) hf₁
  have hi := slice_contains_reachable hw hs₁
  rw [←hf]
  exact map_find_mapm_value hs₂ hi
