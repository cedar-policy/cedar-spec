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

import Cedar.TPE
import Cedar.Thm.TPE.Input
import Cedar.Thm.Validation
import Cedar.Thm.Data.Map

/-!
This file relates what TPE concludes about an entity's attributes and tags to
the concrete entity store.

`entityAttr` draws on two sources: the partial entity data, which refines
the store, and the schema, which every entity in the store conforms to. Each
lemma below discharges one of the four attribute states against those two
sources.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

/-- The `find?` of a value-mapped attribute list follows the source list. -/
private theorem find?_map_value {m : Data.Map Attr Value} {a : Attr} :
  (m.toList.map (λ x => (x.fst, AttrState.value x.snd))).find? (fun x => x.fst == a)
    = (m.find? a).map (λ v => (a, AttrState.value v))
:= by
  rw [← List.find?_pair_map (f := AttrState.value)]
  simp only [Data.Map.find?, Data.Map.toList]
  cases h : (m.1.find? (fun x => x.fst == a)) with
  | none => simp []
  | some p =>
    have hk : p.fst = a := by
      have := List.find?_some h
      simpa using this
    simp only [Option.map_some, hk]

/-- The `absent` entries of `ofConcrete`: `a` is present iff declared and not in `m`. -/
private theorem find?_filter_absent {m : Data.Map Attr Value} {a : Attr}
  (hm : m.find? a = .none) (l : List (Attr × QualifiedType)) :
  ((l.filterMap
      (λ x => if (m.find? x.fst).isSome then none else some (x.fst, AttrState.absent))).find?
      (fun x => x.fst == a)).map Prod.snd
    = if (l.find? (fun x => x.fst == a)).isSome then some AttrState.absent else none
:= by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filterMap_cons, List.find?_cons]
    by_cases hk : hd.fst == a
    · have hka : hd.fst = a := by simpa using hk
      subst hka
      simp only [hm, Option.isSome_none, Bool.false_eq_true, if_false, List.find?_cons,
        beq_self_eq_true, if_true, Option.map_some, Option.isSome_some]
    · cases hopt : (if (m.find? hd.fst).isSome then (none : Option (Attr × AttrState))
          else some (hd.fst, AttrState.absent)) with
      | none => simp only [hk]; rw [ih]
      | some p =>
        have hp : p = (hd.fst, AttrState.absent) := by split at hopt <;> simp_all
        subst hp
        simp only [List.find?_cons, hk]
        rw [ih]

/-- The state `ofConcrete` assigns an attribute: its value if present, `absent`
if declared but missing, and `unknown` if neither declared nor present. -/
theorem ofConcrete_attr {m : Data.Map Attr Value} {rty : RecordType} {a : Attr} :
  (PartialRecord.ofConcrete m rty).attr a
    = match m.find? a with
      | .some v => .value v
      | .none   => if (rty.find? a).isSome then .absent else .unknown
:= by
  simp only [PartialRecord.attr, PartialRecord.ofConcrete, Data.Map.make_find?_eq_list_find?,
    List.find?_append]
  have hrisSome : (rty.find? a).isSome = (rty.toList.find? (fun x => x.fst == a)).isSome := by
    simp only [Data.Map.find?, Data.Map.toList]
    cases rty.1.find? (fun x => x.fst == a) <;> simp
  cases hm : m.find? a with
  | some v =>
    rw [find?_map_value]
    simp only [hm, Option.map_some, Option.some_or, Option.getD_some]
  | none =>
    rw [find?_map_value]
    simp only [hm, Option.map_none, Option.none_or]
    rw [hrisSome, find?_filter_absent hm rty.toList]
    cases hf : (rty.toList.find? (fun x => x.fst == a)).isSome <;> simp []

/-- `attach₂` preserves the key ordering, since it only wraps each element. -/
private theorem sortedBy_attach₂ {α : Type} [SizeOf α] {l : List (Attr × α)}
  (h : l.SortedBy Prod.fst) :
  (l.attach₂).SortedBy (λ x => x.val.fst)
:= by
  refine (List.map_eq_implies_sortedBy (f := Prod.fst) (g := λ x => x.val.fst)
    (xs := l) (ys := l.attach₂) ?_).mp h
  simp only [List.attach₂, List.map_pmap_subtype]

/-- Membership in `attach₂` is membership of the underlying element. -/
theorem mem_attach₂ {α : Type} [SizeOf α] {l : List (Attr × α)}
  {x : { x : Attr × α // sizeOf x.snd < 1 + sizeOf l }} (h : x ∈ l.attach₂) :
  x.val ∈ l
:= by
  simp only [List.attach₂, List.mem_pmap_subtype (h := λ _ => List.sizeOf_snd_lt_sizeOf_list)] at h
  exact h

/-- The concrete record a partial record denotes has exactly the attributes the
partial record denotes a value for. -/
theorem find?_as_values
  {r : PartialRecord} {rty : RecordType} {k : Attr}
  (hrwf : r.WellFormed) :
  (Map.make (r.toList.attach₂.filterMap
    (λ (x : { x : Attr × AttrState // sizeOf x.snd < 1 + sizeOf r.toList }) =>
      (AttrState.asValueAt? x.val.snd (rty.find? x.val.fst)).map (Prod.mk x.val.fst)))).find? k
    = (r.find? k).bind (AttrState.asValueAt? · (rty.find? k))
:= by
  -- the filtered list keeps keys and their order, so it stays sorted
  let g : { x : Attr × AttrState // sizeOf x.snd < 1 + sizeOf r.toList } → Option (Attr × Value) :=
    λ x => (AttrState.asValueAt? x.val.snd (rty.find? x.val.fst)).map (Prod.mk x.val.fst)
  have hg : ∀ x, g x = (AttrState.asValueAt? x.val.snd (rty.find? x.val.fst)).map (Prod.mk x.val.fst) :=
    fun _ => rfl
  have hkey : ∀ x y, g x = some y → x.val.fst = y.fst := by
    intro x y hxy
    rw [hg] at hxy
    cases hs : AttrState.asValueAt? x.val.snd (rty.find? x.val.fst) <;>
      simp only [hs, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hxy
    subst hxy
    rfl
  have hsorted : (r.toList.attach₂.filterMap g).SortedBy Prod.fst := by
    apply List.filterMap_sortedBy (f := (λ x => x.val.fst)) (f' := Prod.fst) hkey
    exact sortedBy_attach₂ (Map.wf_iff_sorted.mp hrwf)
  -- membership in the filtered list comes from the (unique) entry with that key
  have hback : ∀ v, (k, v) ∈ (r.toList.attach₂.filterMap g) →
      (r.find? k).bind (AttrState.asValueAt? · (rty.find? k)) = .some v := by
    intro v hmem
    simp only [List.mem_filterMap] at hmem
    obtain ⟨x, hmem', hgx⟩ := hmem
    have hk := hkey x (k, v) hgx
    simp only at hk
    rw [hg] at hgx
    cases hs : AttrState.asValueAt? x.val.snd (rty.find? x.val.fst) <;>
      simp only [hs, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
        Prod.mk.injEq] at hgx
    obtain ⟨_, hv⟩ := hgx
    subst hv
    have hmemr : x.val ∈ r.toList := mem_attach₂ hmem'
    have hmemk : (k, x.val.snd) ∈ r.toList := by
      have hx : x.val = (k, x.val.snd) := by rw [← hk]
      rw [← hx]; exact hmemr
    rw [(Map.in_list_iff_find?_some hrwf).mp hmemk, Option.bind_some, ← hk]
    exact hs
  cases hfind : (r.find? k).bind (AttrState.asValueAt? · (rty.find? k)) with
  | some v =>
    simp only [Option.bind_eq_some_iff] at hfind
    obtain ⟨sv, hs, hsv⟩ := hfind
    have hmem : (k, v) ∈ (r.toList.attach₂.filterMap g) := by
      simp only [List.mem_filterMap]
      have hmemr : (k, sv) ∈ r.toList := (Map.in_list_iff_find?_some hrwf).mpr hs
      have hp : sizeOf ((k, sv) : Attr × AttrState).snd < 1 + sizeOf r.toList :=
        List.sizeOf_snd_lt_sizeOf_list (by simpa only [Data.Map.toList] using hmemr)
      refine ⟨⟨(k, sv), hp⟩, ?_, ?_⟩
      · simp only [List.attach₂, List.mem_pmap_subtype]
        simpa only [Data.Map.toList] using hmemr
      · rw [hg]; simp only [hsv, Option.map_some]
    exact (Map.in_list_iff_find?_some (Map.make_wf _)).mp (Map.mem_list_mem_make hsorted hmem)
  | none =>
    cases hv : (Map.make (r.toList.attach₂.filterMap g)).find? k with
    | none => rfl
    | some v =>
      have hmem := Map.mem_make_mem_list ((Map.in_list_iff_find?_some (Map.make_wf _)).mpr hv)
      rw [hback v hmem] at hfind
      simp at hfind

/-- The two guarantees `isConcreteAt` provides, per attribute. -/
theorem is_concrete_at_inv {r : PartialRecord} {rty : RecordType}
  (h : r.isConcreteAt rty = true) :
  (∀ k qty, rty.find? k = .some qty → (r.find? k).isSome = true) ∧
  (∀ k s, r.find? k = .some s →
    (match s with
     | .value _ => (rty.find? k).isSome = true
     | .absent  => True
     | .partialRecord r' =>
       ∃ rty', (rty.find? k).map Qualified.getType = .some (.record rty') ∧
         PartialRecord.isConcreteAt r' rty' = true
     | .present
     | .unknown => False))
:= by
  unfold PartialRecord.isConcreteAt at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hA, hB⟩ := h
  constructor
  · intro k qty hqty
    have := hA (k, qty) (by simpa only [Data.Map.toList] using Data.Map.find?_mem_toList hqty)
    simpa only using this
  · intro k s hs
    have hmem : (k, s) ∈ r.toList := Data.Map.find?_mem_toList hs
    have hp : sizeOf ((k, s) : Attr × AttrState).snd < 1 + sizeOf r.toList :=
      List.sizeOf_snd_lt_sizeOf_list (by simpa only [Data.Map.toList] using hmem)
    have hall := hB ⟨(k, s), hp⟩
      ((List.mem_pmap_subtype _ _ (k, s) hp).mpr (by simpa only [Data.Map.toList] using hmem))
    simp only at hall
    cases s with
    | value _ => simpa only using hall
    | absent => trivial
    | present => simp at hall
    | unknown => simp at hall
    | partialRecord r' =>
      cases hd : (rty.find? k).map Qualified.getType with
      | none => rw [hd] at hall; simp at hall
      | some t =>
        cases t <;> rw [hd] at hall <;> try (simp at hall)
        rename_i rty'
        exact ⟨rty', rfl, hall⟩

/--
If a partial record consistent with `m` determines a concrete record, that record
*is* `m` — at every nesting depth.

This is where the closedness of record types is load bearing: consistency alone
says nothing about an attribute the partial record does not mention, but such an
attribute must be undeclared (else it would have to be decided), and so cannot be
present in a record of type `rty`.
-/
theorem as_values_eq
  {env : TypeEnv} {r : PartialRecord} {m m' : Data.Map Attr Value} {rty : RecordType}
  (hrwf : r.WellFormed) (hmwf : m.WellFormed)
  (hinst : InstanceOfType env (.record m) (.record rty))
  (hcons : PartialRecordConsistent r m)
  (hval : r.asValues? rty = .some m') :
  m' = m
:= by
  simp only [PartialRecord.asValues?] at hval
  split at hval
  case isFalse => simp at hval
  case isTrue hdet =>
  simp only [Option.some.injEq] at hval
  subst hval
  apply Map.find?_ext (Map.make_wf _) hmwf
  intro k
  rw [find?_as_values hrwf]
  -- what `isConcreteAt` guarantees per attribute
  obtain ⟨hdecl, hment⟩ := is_concrete_at_inv hdet
  have hc := hcons k
  simp only [PartialRecord.attr] at hc
  cases hfind : r.find? k with
  | none =>
    -- `k` is not mentioned, so `rty` cannot declare it and `m` cannot have it
    have hrty : rty.find? k = .none := by
      cases hd : rty.find? k with
      | none => rfl
      | some qty =>
        have := hdecl k qty hd
        simp only [hfind, Option.isSome_none, Bool.false_eq_true] at this
    simp only [Option.bind_none, absent_attribute_is_absent hinst hrty]
  | some s =>
    rw [hfind] at hc
    simp only [Option.getD_some] at hc
    have hs := hment k s hfind
    simp only [Option.bind_some]
    cases s with
    | value v => simp only [AttrState.asValueAt?, hc.value_inv]
    | absent => simp only [AttrState.asValueAt?, hc.absent_inv]
    | present => simp at hs
    | unknown => simp at hs
    | partialRecord r' =>
      -- the nested record determines a concrete record, which by induction is the
      -- nested concrete record itself
      obtain ⟨m₂, hm₂, hr'wf, hm₂wf, hcons'⟩ := hc.partialRecord_inv
      obtain ⟨rty', hmap, hdet'⟩ := hs
      rw [Option.map_eq_some_iff] at hmap
      obtain ⟨qty, hd, hqt⟩ := hmap
      have hinst' : InstanceOfType env (.record m₂) (.record rty') :=
        instance_of_attribute_type hinst hd hqt hm₂
      have hfold : PartialRecord.asValues? r' rty' = .some
          (Map.make (r'.toList.attach₂.filterMap
            (λ (x : { x : Attr × AttrState // sizeOf x.snd < 1 + sizeOf r'.toList }) =>
              (AttrState.asValueAt? x.val.snd (rty'.find? x.val.fst)).map (Prod.mk x.val.fst)))) := by
        simp only [PartialRecord.asValues?, hdet', if_true]
      have ih := as_values_eq hr'wf hm₂wf hinst' hcons' hfold
      have hqq : qty = .required (.record rty') ∨ qty = .optional (.record rty') := by
        cases qty <;> rename_i t <;> simp only [Qualified.getType] at hqt <;> subst hqt <;> simp
      rcases hqq with hq | hq <;> subst hq <;>
        simp only [AttrState.asValueAt?, hd, hfold, Option.map_some, ih, hm₂]
termination_by sizeOf r
decreasing_by
  have := @sizeOf_attr_lt r k
  simp only [PartialRecord.attr, hfind, Option.getD_some,
    AttrState.partialRecord.sizeOf_spec] at this
  omega

theorem attrs_refine_of_partial_attrs
  {es : Entities} {pes : PartialEntities} {uid : EntityUID} {r : PartialRecord}
  (h_eref : EntitiesRefine es pes)
  (h : PartialEntities.attrs pes uid = .some r) :
  ∃ edata, es.find? uid = .some edata ∧ PartialRecordConsistent r edata.attrs
:= by
  simp only [PartialEntities.attrs, PartialEntities.get, Option.bind_eq_some_iff] at h
  obtain ⟨ped, hped, hattrs⟩ := h
  have h₁ := (h_eref uid ped hped).1
  rw [hattrs] at h₁
  have h₂ : AttrsRefine es uid r := PartialIsValid.some_inv.mp h₁
  exact h₂

theorem tags_refine_of_partial_tags
  {es : Entities} {pes : PartialEntities} {uid : EntityUID} {r : PartialRecord}
  (h_eref : EntitiesRefine es pes)
  (h : PartialEntities.tags pes uid = .some r) :
  ∃ edata, es.find? uid = .some edata ∧ PartialRecordConsistent r edata.tags
:= by
  simp only [PartialEntities.tags, PartialEntities.get, Option.bind_eq_some_iff] at h
  obtain ⟨ped, hped, htags⟩ := h
  have h₁ := (h_eref uid ped hped).2.2
  rw [htags] at h₁
  have h₂ : TagsRefine es uid r := PartialIsValid.some_inv.mp h₁
  exact h₂

/--
`entityAttr` only reaches a conclusion when it has attribute data for `uid` and
the schema declares `uid`'s entity type. In that case the entity is in the store
and conforms to the declared attribute types.
-/
theorem entity_attr_inv
  {env : TypeEnv} {req : Request} {es : Entities} {pes : PartialEntities}
  {uid : EntityUID} {attr : Attr} {s : AttrState}
  (h_wf : InstanceOfWellFormedEnvironment req es env)
  (h_eref : EntitiesRefine es pes)
  (h : entityAttr env pes uid attr = s)
  (hs : s ≠ .unknown) :
  ∃ r rty edata,
    es.find? uid = .some edata ∧
    PartialRecordConsistent r edata.attrs ∧
    InstanceOfType env edata.attrs (.record rty) ∧
    InstanceOfSchemaEntry uid edata env ∧
    r.resolveAttr attr rty = s
:= by
  simp only [entityAttr] at h
  split at h
  case h_2 => exact absurd h.symm hs
  case h_1 r rty hattrs hrty =>
    obtain ⟨edata, hfind, hcons⟩ := attrs_refine_of_partial_attrs h_eref hattrs
    exact ⟨r, rty, edata, hfind, hcons,
      well_typed_entity_attributes h_wf hfind hrty, h_wf.2.2.1 uid edata hfind, h⟩

/-- What `partialRecordIsValid` guarantees about one key of `r`, stated without a `match`. -/
private theorem partialRecordIsValid_entry {schema : Schema} {r : PartialRecord} {rty : RecordType}
  {k : Attr} {s : AttrState}
  (h : partialRecordIsValid schema r rty = true) (hs : r.find? k = .some s) :
  (rty.find? k = .none → s.exists? = false) ∧
  (∀ qty v, rty.find? k = .some qty → s = .value v →
    instanceOfType v qty.getType schema = true) ∧
  (∀ qty, rty.find? k = .some qty → s = .absent → qty.isRequired = false)
:= by
  unfold partialRecordIsValid at h
  simp only [List.all_eq_true, List.attach₂] at h
  have hmem : (k, s) ∈ r.toList := Data.Map.find?_mem_toList hs
  have hp : sizeOf ((k, s) : Attr × AttrState).snd < 1 + sizeOf r.toList :=
    List.sizeOf_snd_lt_sizeOf_list (by simpa only [Data.Map.toList] using hmem)
  have hall := h ⟨(k, s), hp⟩
    ((List.mem_pmap_subtype _ _ (k, s) hp).mpr (by simpa only [Data.Map.toList] using hmem))
  simp only at hall
  split at hall
  case h_1 hd =>
    refine ⟨λ _ => by simpa only [Bool.not_eq_true'] using hall, ?_, ?_⟩
    · intro qty _ hq _; rw [hd] at hq; simp at hq
    · intro qty hq _; rw [hd] at hq; simp at hq
  case h_2 qty hd =>
    refine ⟨λ hn => by rw [hd] at hn; simp at hn, ?_, ?_⟩
    · intro qty' v hq hsv
      rw [hd, Option.some.injEq] at hq
      subst hq
      subst hsv
      simpa only [attrStateIsValidAt] using hall
    · intro qty' hq hsv
      rw [hd, Option.some.injEq] at hq
      subst hq
      subst hsv
      simpa only [Bool.not_eq_true'] using hall

/--
The two obligations `partialRecordIsValid` checks, per attribute: what a declared
attribute may claim, and that anything claimed to exist is declared.
-/
theorem partialRecordIsValid_inv {schema : Schema} {r : PartialRecord} {rty : RecordType}
  (h : partialRecordIsValid schema r rty = true) :
  (∀ k qty, rty.find? k = .some qty →
    (match r.attr k with
     | .value v => instanceOfType v qty.getType schema = true
     | .absent  => qty.isRequired = false
     | _        => True)) ∧
  (∀ k, (r.attr k).exists? = true → (rty.find? k).isSome = true)
:= by
  have hattr : ∀ k, PartialRecord.attr r k = (r.find? k).getD .unknown := λ _ => rfl
  constructor
  · intro k qty hqty
    cases hf : r.find? k with
    | none => rw [hattr, hf]; simp only [Option.getD_none]
    | some s =>
      obtain ⟨_, hval, habs⟩ := partialRecordIsValid_entry h hf
      rw [hattr, hf]
      simp only [Option.getD_some]
      cases s with
      | value v => exact hval qty v hqty rfl
      | absent => exact habs qty hqty rfl
      | partialRecord _ => trivial
      | present => trivial
      | unknown => trivial
  · intro k hex
    cases hf : r.find? k with
    | none =>
      rw [hattr, hf] at hex
      simp only [Option.getD_none, AttrState.exists?, Bool.false_eq_true] at hex
    | some s =>
      obtain ⟨hnone, _, _⟩ := partialRecordIsValid_entry h hf
      rw [hattr, hf] at hex
      simp only [Option.getD_some] at hex
      cases hd : rty.find? k with
      | some _ => simp only [Option.isSome_some]
      | none => rw [hnone hd] at hex; simp at hex

/--
Whatever `resolveAttr` reports about `a` is consistent with the concrete record `m`.

Anything `r` states is returned unchanged, and `PartialRecordConsistent` already says that state is
consistent with `m` — so those cases are immediate and never mention `rty`. The `unknown` case is
the only one that consults the declared type, and it is where the closedness of record types is load
bearing: what `rty` implies about an unstated attribute is sound exactly because `m` conforms to
`rty`.
-/
theorem resolve_attr_consistent
  {env : TypeEnv} {r : PartialRecord} {m : Data.Map Attr Value} {rty : RecordType} {a : Attr}
  (hinst : InstanceOfType env (.record m) (.record rty))
  (hcons : PartialRecordConsistent r m) :
  AttrStateConsistent (r.resolveAttr a rty) (m.find? a)
:= by
  have hc := hcons a
  cases hv : r.attr a with
  | unknown =>
    simp only [PartialRecord.resolveAttr, hv]
    cases hd : rty.find? a with
    | none =>
      simp only [AttrState.ofDeclared, absent_attribute_is_absent hinst hd]
      exact .absent
    | some qty =>
      cases qty with
      | optional aty => simp only [AttrState.ofDeclared]; exact .unknown
      | required aty =>
        obtain ⟨v, hv⟩ := required_attribute_is_present hinst hd
        simp only [AttrState.ofDeclared, hv]
        exact .present
  | value v | partialRecord r' | present | absent =>
    all_goals rw [hv] at hc
    all_goals simp only [PartialRecord.resolveAttr, hv]
    all_goals exact hc

/-- Everything `entityAttr` reports about an attribute is true of the store. -/
theorem entity_attr_consistent
  {env : TypeEnv} {req : Request} {es : Entities} {pes : PartialEntities}
  {uid : EntityUID} {attr : Attr}
  (h_wf : InstanceOfWellFormedEnvironment req es env)
  (h_eref : EntitiesRefine es pes) :
  AttrStateConsistent (entityAttr env pes uid attr) ((es.attrsOrEmpty uid).find? attr)
:= by
  simp only [entityAttr]
  split
  case h_2 => exact .unknown
  case h_1 r rty hattrs hrty =>
    obtain ⟨edata, hfind, hcons⟩ := attrs_refine_of_partial_attrs h_eref hattrs
    have hinst := well_typed_entity_attributes h_wf hfind hrty
    simp only [Entities.attrsOrEmpty, hfind]
    exact resolve_attr_consistent hinst hcons

/-- A known attribute value is the value the concrete store has. -/
theorem entity_attr_value
  {env : TypeEnv} {req : Request} {es : Entities} {pes : PartialEntities}
  {uid : EntityUID} {attr : Attr} {v : Value}
  (h_wf : InstanceOfWellFormedEnvironment req es env)
  (h_eref : EntitiesRefine es pes)
  (h : entityAttr env pes uid attr = .value v) :
  ∃ edata, es.find? uid = .some edata ∧ edata.attrs.find? attr = .some v ∧
    InstanceOfSchemaEntry uid edata env
:= by
  obtain ⟨r, rty, edata, hfind, hcons, hinst, hentry, hres⟩ :=
    entity_attr_inv h_wf h_eref h (by simp)
  have hc := resolve_attr_consistent (a := attr) hinst hcons
  rw [hres] at hc
  exact ⟨edata, hfind, hc.value_inv, hentry⟩

/-- An attribute reported absent really is absent from the concrete store. -/
theorem entity_attr_absent
  {env : TypeEnv} {req : Request} {es : Entities} {pes : PartialEntities}
  {uid : EntityUID} {attr : Attr}
  (h_wf : InstanceOfWellFormedEnvironment req es env)
  (h_eref : EntitiesRefine es pes)
  (h : entityAttr env pes uid attr = .absent) :
  (es.attrsOrEmpty uid).find? attr = .none
:= by
  have hc := entity_attr_consistent (uid := uid) (attr := attr) h_wf h_eref
  rw [h] at hc
  exact hc.absent_inv

/-- An attribute reported to exist really is present in the concrete store. -/
theorem entity_attr_exists
  {env : TypeEnv} {req : Request} {es : Entities} {pes : PartialEntities}
  {uid : EntityUID} {attr : Attr}
  (h_wf : InstanceOfWellFormedEnvironment req es env)
  (h_eref : EntitiesRefine es pes)
  (h : (entityAttr env pes uid attr).exists? = true) :
  ∃ v, (es.attrsOrEmpty uid).find? attr = .some v
:= AttrStateConsistent.exists_inv h (entity_attr_consistent h_wf h_eref)

/-- Everything `entityTag` reports about a tag is true of the store.

Tags need no schema input: they have no declared key set, so a tag the partial
data does not mention stays `unknown`. -/
theorem entity_tag_consistent
  {es : Entities} {pes : PartialEntities} {uid : EntityUID} {tag : Tag}
  (h_eref : EntitiesRefine es pes) :
  AttrStateConsistent (entityTag pes uid tag) ((es.tagsOrEmpty uid).find? tag)
:= by
  simp only [entityTag]
  split
  case h_2 => exact .unknown
  case h_1 r htags =>
    obtain ⟨edata, hfind, hcons⟩ := tags_refine_of_partial_tags h_eref htags
    simp only [Entities.tagsOrEmpty, hfind]
    exact hcons tag

/-- A known tag value is the value the concrete store has. -/
theorem entity_tag_value
  {es : Entities} {pes : PartialEntities} {uid : EntityUID} {tag : Tag} {v : Value}
  (h_eref : EntitiesRefine es pes)
  (h : entityTag pes uid tag = .value v) :
  ∃ edata, es.find? uid = .some edata ∧ edata.tags.find? tag = .some v
:= by
  simp only [entityTag] at h
  split at h
  case h_2 => simp at h
  case h_1 r htags =>
    obtain ⟨edata, hfind, hcons⟩ := tags_refine_of_partial_tags h_eref htags
    have hc := hcons tag
    rw [h] at hc
    exact ⟨edata, hfind, hc.value_inv⟩

/-- A tag reported absent really is absent from the concrete store. -/
theorem entity_tag_absent
  {es : Entities} {pes : PartialEntities} {uid : EntityUID} {tag : Tag}
  (h_eref : EntitiesRefine es pes)
  (h : entityTag pes uid tag = .absent) :
  (es.tagsOrEmpty uid).find? tag = .none
:= by
  have hc := entity_tag_consistent (uid := uid) (tag := tag) h_eref
  rw [h] at hc
  exact hc.absent_inv

/-- A tag reported to exist really is present in the concrete store. -/
theorem entity_tag_exists
  {es : Entities} {pes : PartialEntities} {uid : EntityUID} {tag : Tag}
  (h_eref : EntitiesRefine es pes)
  (h : (entityTag pes uid tag).exists? = true) :
  ∃ v, (es.tagsOrEmpty uid).find? tag = .some v
:= AttrStateConsistent.exists_inv h (entity_tag_consistent h_eref)

/-- `find?` on the partial view of a concrete store. -/
theorem find?_as_partial {ets : EntitySchema} {es : Entities} {uid : EntityUID} :
  (Entities.asPartial ets es).find? uid
    = (es.find? uid).map (EntityData.asPartial · (attrsOrEmpty ets uid.ty))
:= by
  simp only [Entities.asPartial, Map.find?, Map.toList]
  induction es.1 with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨k, d⟩ := hd
    simp only [List.map_cons, List.find?_cons]
    cases hk : k == uid
    · simpa only [Bool.false_eq_true, if_false, hk] using ih
    · have hkeq : k = uid := eq_of_beq hk
      subst hkeq
      simp only [Option.map_some]

end Cedar.Thm
