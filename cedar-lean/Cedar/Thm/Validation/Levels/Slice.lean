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
:= by
  simp [Entities.attrs, Map.findOrErr] at he
  split at he <;> simp at he
  rename_i ed h₁
  exists ed

theorem entities_find?_then_attrs {entities: Entities} {ed : EntityData} {uid : EntityUID}
  (he : entities.find? uid = some ed)
  : .ok ed.attrs = entities.attrs uid
:= by
  simp [Entities.attrs, Map.findOrErr]
  split <;> simp
  · rename_i he'
    rw [he'] at he
    injections he
    simp [he]
  · rename_i h₁
    simp [he] at h₁

theorem entities_tags_then_find? {entities: Entities} {tags : Map Tag Value} {uid : EntityUID}
  (he : entities.tags uid = .ok tags)
  : ∃ ed, entities.find? uid = some ed ∧ ed.tags = tags
:= by
  simp [Entities.tags, Map.findOrErr] at he
  split at he <;> simp at he
  rename_i ed h₁
  exists ed

theorem entities_find?_then_tags {entities: Entities} {ed : EntityData} {uid : EntityUID}
  (he : entities.find? uid = some ed)
  : .ok ed.tags = entities.tags uid
:= by
  simp [Entities.tags, Map.findOrErr]
  split <;> simp
  · rename_i he'
    rw [he'] at he
    injections he
    simp [he]
  · rename_i h₁
    simp [he] at h₁

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

inductive EuidViaPath : Value → List Attr → EntityUID → Prop where
  | euid (euid : EntityUID) :
    EuidViaPath (.prim (.entityUID euid)) [] euid
  | record {a : Attr} {path : List Attr} {attrs : Map Attr Value}
    (ha : attrs.find? a = some v)
    (hv : EuidViaPath v path euid) :
    EuidViaPath (.record attrs)  (a :: path) euid

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
  (hv : EuidViaPath v path euid)
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

def CheckedEvalEntityReachable (e : Expr) :=
  ∀ {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {request : Request} {entities : Entities} {v: Value} {path : List Attr} {euid : EntityUID},
    CapabilitiesInvariant c request entities →
    RequestAndEntitiesMatchEnvironment env request entities →
    typeOf e c env = .ok (tx, c') →
    AtLevel tx n →
    ¬ EntityLitViaPath tx path →
    evaluate e request entities = .ok v →
    EuidViaPath v path euid →
    entities.contains euid →
    ReachableIn entities request.sliceEUIDs euid (n + 1)

theorem non_entity_lit_not_euid_via_path {p : Prim} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {entities : Entities} {path : List Attr}
  (ht : typeOf (.lit p) c env = .ok (tx, c'))
  (he : evaluate (.lit p) request entities = .ok v)
  (hel : ¬ EntityLitViaPath tx path) :
  ¬ EuidViaPath v path euid
:= by
  intro ha
  cases p
  case entityUID =>
    replace ⟨ _, ht ⟩ := type_of_lit_inversion ht
    rw [←ht] at hel
    exact hel (by constructor)
  all_goals
    simp only [evaluate, Except.ok.injEq] at he
    subst he
    cases ha

theorem var_entity_reachable {var : Var} {v : Value} {n : Nat} {request : Request} {entities : Entities} {euid : EntityUID} {path : List Attr}
  (he : evaluate (.var var) request entities = .ok v)
  (ha : EuidViaPath v path euid)
  (hf : entities.contains euid) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  have hi : euid ∈ request.sliceEUIDs := by
    rw [Request.sliceEUIDs, Set.mem_union_iff_mem_or, ←Set.make_mem]
    cases var <;> simp only [evaluate, Except.ok.injEq] at he <;> subst he <;> cases ha
    case principal | action | resource => simp [hf]
    case context v a path hf' hv =>
      right
      unfold Value.sliceEUIDs List.attach₃
      simp only [List.map_pmap_subtype (λ e : (Attr × Value) => e.snd.sliceEUIDs) request.4.1, set_mem_union_all_iff_mem_any, List.mem_map, Prod.exists]
      exists v.sliceEUIDs
      constructor
      · exists a, v
        replace hf' := Map.find?_mem_toList hf'
        unfold Map.toList at hf'
        simp [hf']
      · exact in_val_then_val_slice hv
  exact ReachableIn.in_start hi

theorem checked_eval_entity_reachable_ite {e₁ e₂ e₃: Expr} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {entities : Entities} {path : List Attr}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf (.ite e₁ e₂ e₃) c env = .ok (tx, c'))
  (hl : AtLevel tx n)
  (hel : ¬ EntityLitViaPath tx path)
  (he : evaluate (.ite e₁ e₂ e₃) request entities = .ok v)
  (ha : EuidViaPath v path euid)
  (hf : entities.contains euid)
  (ih₂ : CheckedEvalEntityReachable e₂)
  (ih₃ : CheckedEvalEntityReachable e₃) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  have ⟨tx₁, bty₁, c₁, tx₂, c₂, tx₃, c₃, htx, htx₁, hty₁, hif ⟩ := type_of_ite_inversion ht
  have ⟨ hgc, v, he₁, hi₁⟩ := type_of_is_sound hc hr htx₁

  rw [htx] at hl
  cases hl
  rename_i hl₁ hl₂ hl₃

  rw [htx] at hel
  have hel₂ : ¬ EntityLitViaPath tx₂ path := by
    intros hel₂
    exact hel (EntityLitViaPath.ite_true hel₂)
  have hel₃ : ¬ EntityLitViaPath tx₃ path := by
    intros hel₃
    exact hel (EntityLitViaPath.ite_false hel₃)

  simp only [evaluate] at he
  cases he₁ : Result.as Bool (evaluate e₁ request entities) <;> simp only [he₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at he
  simp only [Result.as, Coe.coe, Value.asBool] at he₁
  split at he₁ <;> try contradiction
  split at he₁ <;> try contradiction
  injections he₁
  subst he₁
  rename_i _ b he₁'
  replace he₁ : Value.prim (Prim.bool b) = v := by
    unfold EvaluatesTo at he₁
    simp only [he₁', reduceCtorEq, Except.ok.injEq, false_or] at he₁
    exact he₁
  subst he₁

  split at he
  case isTrue hb =>
    subst hb
    have htx₂ : typeOf e₂ (c ∪ c₁) env = .ok (tx₂, c₂) := by
      split at hif <;> try simp only [hif]
      rw [hty₁] at hi₁
      have := instance_of_ff_is_false hi₁
      contradiction
    replace hgc : CapabilitiesInvariant c₁ request entities := by
      simp only [he₁', GuardedCapabilitiesInvariant, forall_const] at hgc
      exact hgc
    exact ih₂ (capability_union_invariant hc hgc) hr htx₂ hl₂ hel₂ he ha hf
  case isFalse hb =>
    replace hb : b = false := by
      cases b <;> simp only [Bool.true_eq_false] <;> contradiction
    subst hb
    have htx₃ : typeOf e₃ c env = .ok (tx₃, c₃) := by
      split at hif <;> try simp only [hif]
      rw [hty₁] at hi₁
      have := instance_of_tt_is_true hi₁
      contradiction
    exact ih₃ hc hr htx₃ hl₃ hel₃ he ha hf

theorem and_not_euid_via_path {e₁ e₂: Expr} {entities : Entities} {path : List Attr}
  (he : evaluate (.and e₁ e₂) request entities = .ok v) :
  ¬ EuidViaPath v path euid
:= by
  intro ha
  simp only [evaluate] at he
  cases he₁ :  Result.as Bool (evaluate e₁ request entities) <;>
    simp only [he₁, bind_pure_comp, Except.bind_err, Except.bind_ok, reduceCtorEq] at he
  split at he
  · injections he
    subst he ; cases ha
  · cases he₂ : Result.as Bool (evaluate e₂ request entities) <;>
      simp only [he₂, Except.map_error, reduceCtorEq, Except.map_ok, Except.ok.injEq] at he
    subst he ; cases ha

theorem or_not_euid_via_path {e₁ e₂: Expr} {entities : Entities} {path : List Attr}
  (he : evaluate (.or e₁ e₂) request entities = .ok v) :
  ¬ EuidViaPath v path euid
:= by
  intro ha
  simp only [evaluate] at he
  cases he₁ : Result.as Bool (evaluate e₁ request entities) <;>
    simp only [he₁, bind_pure_comp, Except.bind_err, Except.bind_ok, reduceCtorEq] at he
  split at he
  · simp at he
    subst he ; cases ha
  · cases he₂ : Result.as Bool (evaluate e₂ request entities) <;>
      simp only [he₂, Except.map_error, reduceCtorEq, Except.map_ok, Except.ok.injEq] at he
    subst he ; cases ha

theorem unary_not_euid_via_path {op : UnaryOp} {e₁ : Expr} {entities : Entities} {path : List Attr}
  (he : evaluate (.unaryApp op e₁) request entities = .ok v) :
  ¬ EuidViaPath v path euid
:= by
  intro ha
  simp only [evaluate] at he
  cases he₁ : evaluate e₁ request entities <;>
    simp [he₁, intOrErr, apply₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at he
  (split at he <;> try split at he) <;>
  try simp only [reduceCtorEq] at he
  all_goals { injections he ; subst he ; cases ha }

theorem reachable_tag_step {n : Nat} {euid euid' : EntityUID} {start : Set EntityUID} {entities : Entities} {ed : EntityData} {tag : Tag} {path : List Attr}
  (hr : ReachableIn entities start euid n)
  (he₁ : entities.find? euid = some ed)
  (he₂ : ed.tags.find? tag = some tv)
  (he₃ : EuidViaPath tv path euid') :
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

theorem checked_eval_entity_reachable_binary {op : BinaryOp} {e₁ e₂: Expr} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {entities : Entities} {path : List Attr}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf (.binaryApp op e₁ e₂) c env = .ok (tx, c'))
  (hl : AtLevel tx n)
  (hel : ¬ EntityLitViaPath tx path)
  (he : evaluate (.binaryApp op e₁ e₂) request entities = .ok v)
  (ha : EuidViaPath v path euid)
  (ih₁ : CheckedEvalEntityReachable e₁) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  simp only [evaluate] at he
  cases he₁ : evaluate e₁ request entities <;> simp only [he₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at he
  cases he₂ : evaluate e₂ request entities <;> simp [he₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at he
  simp only [apply₂, intOrErr, inₛ, hasTag, getTag] at he

  (split at he <;> try split at he) <;>
  try contradiction

  case h_13 euid' tag =>
    have ⟨hc', ety, ty, tx₁, tx₂, c₁', c₂', htx₁, hty₁, htx₂, hty₂, ht, htx, hc₁⟩ := type_of_getTag_inversion ht
    subst htx hc'
    cases hl
    case binaryApp hop _  _ =>
      simp [DereferencingBinaryOp] at hop
    case getTag hrt₁ hl₁ hl₂ =>
      cases he₃ : entities.tags euid' <;> simp only [he₃, Except.bind_ok, Except.bind_err, reduceCtorEq] at he
      simp only [Map.findOrErr] at he
      split at he <;> simp only [reduceCtorEq, Except.ok.injEq] at he
      subst he
      rename_i hv

      have ⟨ ed, hed, hed' ⟩ := entities_tags_then_find? he₃
      subst hed'
      have hf' : entities.contains euid' := by simp [Map.contains, Option.isSome, hed]

      have ih := ih₁ hc hr htx₁ hl₁ hrt₁ he₁ (.euid euid') hf'
      exact reachable_tag_step ih hed hv ha

  case h_11 vs =>
    cases he₃ : Set.mapOrErr Value.asEntityUID vs Error.typeError <;> simp [he₃] at he
    subst he ; cases ha
  all_goals { injections he ; subst he ; cases ha }

theorem reachable_attr_step {n : Nat} {euid euid' : EntityUID} {start : Set EntityUID} {entities : Entities} {ed : EntityData} {path : List Attr}
  (hr : ReachableIn entities start euid n)
  (he₁: entities.find? euid = some ed)
  (he₂ : EuidViaPath (.record ed.attrs) path euid' ) :
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

theorem checked_eval_entity_reachable_get_attr {e : Expr} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {entities : Entities} {path : List Attr}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf (e.getAttr a) c env = .ok (tx, c'))
  (hl : AtLevel tx n)
  (hel : ¬ EntityLitViaPath tx path)
  (he : evaluate (e.getAttr a) request entities = .ok v)
  (ha : EuidViaPath v path euid)
  (hf : entities.contains euid)
  (ih : CheckedEvalEntityReachable e) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  simp only [evaluate] at he
  cases he₁ : evaluate e request entities <;> simp only [he₁, Except.bind_err, reduceCtorEq] at he
  have ⟨ hc', tx', c₁', ht', htx, h₂ ⟩ := type_of_getAttr_inversion ht
  rw [htx] at hl
  have ⟨ hgc, v, he', hi ⟩ := type_of_is_sound hc hr ht'
  cases hl
  case getAttr n hel hl hety  =>
    have ⟨euid', hv⟩ : ∃ euid', v = Value.prim (Prim.entityUID euid') := by
      rw [hety] at hi
      have ⟨ euid', hety, hv⟩ := instance_of_entity_type_is_entity hi
      simp [hv]
    subst hv

    rename_i v₁' _
    have hv : v₁' = Value.prim (Prim.entityUID euid') := by
      unfold EvaluatesTo at he'
      rw [he₁] at he'
      cases he' <;> rename_i he' <;> simp only [reduceCtorEq, Except.ok.injEq, false_or] at he'
      exact he'
    subst hv

    simp only [getAttr, attrsOf, Except.bind_ok] at he
    cases he₂ : entities.attrs euid' <;> simp only [he₂, Except.bind_err, reduceCtorEq] at he
    rename_i attrs
    simp only [Map.findOrErr, Except.bind_ok] at he
    split at he <;> simp only [reduceCtorEq, Except.bind_ok, Except.ok.injEq] at he
    subst he
    rename_i v hv

    have ⟨ ed, hed, hed' ⟩ := entities_attrs_then_find? he₂
    subst attrs
    have hf' : entities.contains euid' := by simp [Map.contains, Option.isSome, hed]
    have ih := ih hc hr ht' hl hel he₁ (.euid euid') hf'
    have ha' : EuidViaPath (Value.record ed.attrs) (a :: path) euid := .record hv ha
    apply reachable_attr_step ih hed ha'

  case getAttrRecord hty hl =>
    cases h₂ <;> rename_i h₂
    · replace ⟨ ety, h₂ ⟩ := h₂
      specialize hty ety h₂
      contradiction
    · replace ⟨ rty, h₂ ⟩ := h₂
      rw [h₂] at hi
      have ⟨ attrs, hv⟩ := instance_of_record_type_is_record hi ; clear hi
      subst hv
      unfold EvaluatesTo at he'
      rw [he₁] at he'
      cases he' <;> rename_i he' <;> simp only [reduceCtorEq, Except.ok.injEq, false_or] at he'
      subst he'
      simp only [getAttr, attrsOf, Map.findOrErr, Except.bind_ok] at he
      split at he <;> simp only [reduceCtorEq, Except.ok.injEq] at he
      rename_i v hv
      subst he
      have ha' : EuidViaPath (Value.record attrs) (a :: path) euid := .record hv ha
      have hrt' : ¬ EntityLitViaPath tx' (a :: path) := by
        rw [htx] at hel
        intros hel'
        apply hel
        constructor
        assumption
      exact ih hc hr ht' hl hrt' he₁ ha' hf

theorem has_attr_not_euid_via_path {e₁ : Expr} {a : Attr} {entities : Entities} {path : List Attr}
  (he : evaluate (.hasAttr e₁ a) request entities = .ok v) :
  ¬ EuidViaPath v path euid
:= by
  intro ha
  simp only [evaluate] at he
  cases he₁ : evaluate e₁ request entities <;>
    simp only [he₁, Except.bind_err, reduceCtorEq, hasAttr, Except.bind_ok] at he
  rename_i v₁
  cases he₂ : attrsOf v₁ λ uid => Except.ok (entities.attrsOrEmpty uid) <;>
    simp only [he₂, Except.ok.injEq, Except.bind_ok, Except.bind_err, reduceCtorEq] at he
  subst he ; cases ha

theorem set_not_euid_via_path {xs : List Expr} {entities : Entities} {path : List Attr}
  (he : evaluate (.set xs) request entities = .ok v) :
  ¬ EuidViaPath v path euid
:= by
  intro ha
  simp only [evaluate] at he
  cases he₁ : (xs.mapM₁ (λ x => evaluate x.val request entities)) <;>
    simp [he₁, Except.bind_err, Except.bind_ok, Except.ok.injEq] at he
  subst he ; cases ha

theorem record_value_contains_evaluated_attrs
  (he : evaluate (.record rxs) request entities = .ok (.record rvs))
  (hfv : rvs.find? a = some av) :
  ∃ x, (Map.make rxs).find? a = some x ∧ evaluate x request entities = .ok av
:= by
  simp only [evaluate] at he
  cases he₁ : rxs.mapM₂ fun x => bindAttr x.1.fst (evaluate x.1.snd request entities) <;>
    simp? [he₁, Except.bind_err, reduceCtorEq, Except.bind_ok, Except.ok.injEq, Value.record.injEq] at he
  rw [←he] at hfv
  rename_i rvs
  rw [List.mapM₂, List.attach₂] at he₁
  rw [List.mapM_pmap_subtype λ (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd request entities)] at he₁
  rw [List.mapM_ok_iff_forall₂] at he₁
  simp only [Map.make, Map.find?, Map.kvs] at *
  split at hfv <;> simp at hfv
  subst hfv
  rename_i a v hfv
  have hfv' := List.find?_some hfv
  simp only [beq_iff_eq] at hfv'
  subst hfv'
  replace he₁ : List.Forallᵥ (λ x y => evaluate x request entities = Except.ok y) rxs rvs := by
    simp only [List.forallᵥ_def]
    apply List.Forall₂.imp _ he₁
    intro x y h
    simp only [bindAttr] at h
    cases hx : evaluate x.snd request entities <;> simp [hx] at h
    simp only [← h, and_self]
  replace he₁ := List.canonicalize_preserves_forallᵥ _ _ _ he₁
  simp only [List.forallᵥ_def] at he₁
  have ⟨(a', x), he₂, he₃, he₄⟩ := List.forall₂_implies_all_right he₁ (a, v) (List.mem_of_find?_eq_some hfv)
  simp only at he₃ he₄
  subst he₃
  exists x
  simp only [List.mem_of_sortedBy_implies_find? he₂ (List.canonicalize_sortedBy _ _), he₄, and_self]

theorem checked_eval_entity_reachable_record {rxs : List (Attr × Expr)} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {entities : Entities} {path : List Attr}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf (.record rxs) c env = .ok (tx, c'))
  (hl : AtLevel tx n)
  (hel : ¬ EntityLitViaPath tx path)
  (he : evaluate (.record rxs) request entities = .ok v)
  (ha : EuidViaPath v path euid)
  (hf : entities.contains euid)
  (ih : forall a x, (Map.make rxs).find? a = some x → CheckedEvalEntityReachable x) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  have ⟨ hc', rtxs, htx, hfat ⟩ := type_of_record_inversion ht
  subst hc' htx

  have ⟨ rvs, hv ⟩ : ∃ rvs, Value.record rvs = v := by
    simp only [evaluate] at he
    cases he₁ : rxs.mapM₂ fun x => bindAttr x.1.fst (evaluate x.1.snd request entities) <;>
      simp only [he₁, Except.bind_ok, Except.ok.injEq, Except.bind_err, reduceCtorEq] at he
    simp [←he]
  subst hv
  cases ha
  rename_i v a path' hfv hv
  have ⟨ x, hfx, hex ⟩ := record_value_contains_evaluated_attrs he hfv

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
    simp only [ht'', Except.ok.injEq, Prod.mk.injEq] at haty₂
    simp only [haty]
    simp [←haty₂, ht'', hf'']

  unfold AttrExprHasAttrType at het
  simp only [Prod.mk.injEq, true_and, exists_and_left] at het
  replace ⟨_, het ⟩ := het

  have hl' : AtLevel atx n := by
    cases hl
    rename_i hl
    exact hl (a, atx) (Map.make_mem_list_mem (Map.find?_mem_toList hfatx))

  have hel' : ¬ EntityLitViaPath atx path' := by
    intro hel'
    apply hel
    exact EntityLitViaPath.record hfatx hel'

  exact ih a x hfx hc hr het hl' hel' hex hv hf

theorem call_not_euid_via_path {xfn : ExtFun} {xs : List Expr} {entities : Entities} {path : List Attr}
  (he : evaluate (.call xfn xs) request entities = .ok v) :
  ¬ EuidViaPath v path euid
:= by
  intro ha
  simp only [evaluate] at he
  cases he₁ : xs.mapM₁ fun x => evaluate x.val request entities <;>
    simp only [he₁, Except.bind_err, reduceCtorEq] at he

  simp only [call, res, Except.bind_ok] at he
  (split at he <;> try split at he) <;>
  simp only [Except.ok.injEq, reduceCtorEq] at he

  all_goals { subst he ; cases ha }

/--
If an expression checks at level `n` and then evaluates an entity (or a record
containing an entity), then that entity must reachable in `n + 1` steps.
-/
theorem checked_eval_entity_reachable {e : Expr} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {request : Request} {entities : Entities} {v : Value} {path : List Attr} {euid : EntityUID}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : AtLevel tx n)
  (hel : ¬ EntityLitViaPath tx path)
  (he : evaluate e request entities = .ok v)
  (ha : EuidViaPath v path euid)
  (hf : entities.contains euid) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  cases e
  case lit =>
    exfalso
    exact non_entity_lit_not_euid_via_path ht he hel ha

  case var =>
    exact var_entity_reachable he ha hf

  case ite e₁ e₂ e₃ =>
    have ih₂ := @checked_eval_entity_reachable e₂
    have ih₃ := @checked_eval_entity_reachable e₃
    exact checked_eval_entity_reachable_ite hc hr ht hl hel he ha hf ih₂ ih₃

  case and =>
    exfalso
    exact and_not_euid_via_path he ha

  case or e=>
    exfalso
    exact or_not_euid_via_path he ha

  case unaryApp op e =>
    exfalso
    exact unary_not_euid_via_path he ha

  case binaryApp op e₁ e₂ =>
    have ih₁ := @checked_eval_entity_reachable e₁
    exact checked_eval_entity_reachable_binary hc hr ht hl hel he ha ih₁

  case getAttr e _ =>
    have ih := @checked_eval_entity_reachable e
    exact checked_eval_entity_reachable_get_attr hc hr ht hl hel he ha hf ih

  case hasAttr e a =>
    exfalso
    exact has_attr_not_euid_via_path he ha

  case set es =>
    exfalso
    exact set_not_euid_via_path he ha

  case record rxs =>
    have ih : forall a x, (Map.make rxs).find? a = some x → CheckedEvalEntityReachable x := by
      intros a x hfx
      have : sizeOf x < sizeOf (Expr.record rxs) := by
        replace he := Map.make_mem_list_mem (Map.find?_mem_toList hfx)
        have h₁ := List.sizeOf_lt_of_mem he
        rw [Prod.mk.sizeOf_spec a x] at h₁
        simp only [Expr.record.sizeOf_spec, gt_iff_lt]
        omega
      exact @checked_eval_entity_reachable x
    exact checked_eval_entity_reachable_record hc hr ht hl hel he ha hf ih

  case call xfn args =>
    exfalso
    exact call_not_euid_via_path he ha
termination_by e

theorem in_work_then_in_slice {entities : Entities} {work slice : Set EntityUID} {euid : EntityUID} {n : Nat}
  (hw : euid ∈ work)
  (hs : Entities.sliceAtLevel.sliceAtLevel entities work (n + 1) = some slice)
  : euid ∈ slice
:= by
  unfold Entities.sliceAtLevel.sliceAtLevel at hs
  cases hs₁ :
    List.mapM (Map.find? entities) work.elts
  <;> simp only [hs₁, Option.map_eq_map, Option.bind_eq_bind, Option.bind_none_fun, reduceCtorEq] at hs
  rename_i eds
  cases hs₂ :
    List.mapM (λ x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs n) eds
  <;> simp only [hs₂, Option.map_none', Option.map_some', Option.none_bind, Option.some_bind, reduceCtorEq,Option.some.injEq] at hs
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
  rewrite [←level_spec] at hl
  have hw : ReachableIn entities request.sliceEUIDs euid (n + 1) :=
    checked_eval_entity_reachable hc hr ht hl hrt he (.euid euid) hf₁
  have hi := slice_contains_reachable hw hs₁
  rw [←hf]
  exact map_find_mapm_value hs₂ hi
