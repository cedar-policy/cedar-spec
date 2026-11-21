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

import CedarGen.Relational.SchemaGenFSound

/-! # `GenTypeEnvF` is complete

* every environment satisfying `EnvAssumptions` within the budget is generated with every flag
  `false` (`GenTypeEnvF.complete_envAssumptions`);
* every `TypeEnvWF` environment within the budget is generated with the four `wf` flags
  (`GenTypeEnvF.complete_typeEnvWF`).

Both take the `dense` mode, whose `free` rules draw any parents. Ranks, which only matter with
`wfActs`, are the number of an action's ancestors among the actions: an ancestor has strictly
fewer (`rank_lt`), by transitivity and irreflexivity. -/

namespace Cedar.Validation.Relational.SchemaGen

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Cedar.Validation.Relational.Schema

/-! ## The skeleton of an environment -/

/-- Whether an entry is an enumeration. -/
def isEnum : EntitySchemaEntry → Bool
  | .standard _ => false
  | .enum _ => true

def kindsOf (ents : List (EntityType × EntitySchemaEntry)) : List (EntityType × Bool) :=
  ents.map fun p => (p.1, isEnum p.2)

def stdOf (ents : List (EntityType × EntitySchemaEntry)) : List EntityType :=
  (ents.filter fun p => !isEnum p.2).map Prod.fst

def enumOf (ents : List (EntityType × EntitySchemaEntry)) : List EntityType :=
  (ents.filter fun p => isEnum p.2).map Prod.fst

theorem kinds_kindsOf : ∀ ents : List (EntityType × EntitySchemaEntry),
    Kinds (ents.map Prod.fst) (kindsOf ents)
  | [] => .nil
  | (x, .standard _) :: ents => .cons _ _ _ _ .std (kinds_kindsOf ents)
  | (x, .enum _) :: ents => .cons _ _ _ _ .enum (kinds_kindsOf ents)

theorem stdNames_kindsOf : ∀ ents : List (EntityType × EntitySchemaEntry),
    StdNames (kindsOf ents) (stdOf ents)
  | [] => .nil
  | (x, .standard _) :: ents => by
    simp only [kindsOf, stdOf, List.map_cons, isEnum, List.filter_cons, Bool.not_false,
      ↓reduceIte]
    exact .std _ _ _ (stdNames_kindsOf ents)
  | (x, .enum _) :: ents => by
    simp only [kindsOf, stdOf, List.map_cons, isEnum, List.filter_cons, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
    exact .enum _ _ _ (stdNames_kindsOf ents)

theorem enumNames_kindsOf : ∀ ents : List (EntityType × EntitySchemaEntry),
    EnumNames (kindsOf ents) (enumOf ents)
  | [] => .nil
  | (x, .standard _) :: ents => by
    simp only [kindsOf, enumOf, List.map_cons, isEnum, List.filter_cons, Bool.false_eq_true,
      ↓reduceIte]
    exact .std _ _ _ (enumNames_kindsOf ents)
  | (x, .enum _) :: ents => by
    simp only [kindsOf, enumOf, List.map_cons, isEnum, List.filter_cons, ↓reduceIte]
    exact .enum _ _ _ (enumNames_kindsOf ents)

theorem typesOf_map : ∀ us : List EntityUID, TypesOf us (us.map (·.ty))
  | [] => .nil
  | ⟨ty, eid⟩ :: us => .cons _ _ _ _ (typesOf_map us)

theorem ranked_map {β} (f : EntityUID × β → Nat) : ∀ l : List (EntityUID × β),
    Ranked (l.map Prod.fst) (l.map fun p => (p.1, f p))
  | [] => .nil
  | p :: l => .cons _ _ _ _ (.mk _) (ranked_map f l)

theorem rawNames_of {i} : ∀ {xs : List EntityType}, (∀ x ∈ xs, NameIf i x) → RawNames i xs
  | [], _ => .nil _
  | x :: xs, h => .cons _ _ _ (h x List.mem_cons_self)
      (rawNames_of fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem rawUids_of {a i ks} : ∀ {us : List EntityUID}, (∀ u ∈ us, ActTyOK a i ks u.ty) →
    RawUids a i ks us
  | [], _ => .nil _ _ _
  | ⟨ty, eid⟩ :: us, h => .cons _ _ _ _ _ _ (h _ List.mem_cons_self)
      (rawUids_of fun u hu => h u (List.mem_cons_of_mem _ hu))

theorem rawStrs_of : ∀ xs : List String, RawStrs xs
  | [] => .nil
  | x :: xs => .cons _ _ (rawStrs_of xs)

theorem appliesF_of {d i ks ats} : ∀ {xs : List EntityType}, (∀ x ∈ xs, RefIf d i ks ats x) →
    AppliesF d i ks ats xs
  | [], _ => .nil _ _ _ _
  | x :: xs, h => .cons _ _ _ _ _ _ (h x List.mem_cons_self)
      (appliesF_of fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem appliesBounded_of {d i ks ats} : ∀ {xs : List EntityType} {n : Nat},
    AppliesF d i ks ats xs → xs.length ≤ n → AppliesBounded d i ks ats n xs
  | [], _, _, _ => .nil _ _ _ _ _
  | x :: xs, n, h, hn => by
    cases h
    case cons hx hxs =>
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
      exact .cons _ _ _ _ _ _ _ hx (appliesBounded_of hxs (by simp only [List.length_cons] at hn; omega))

theorem appliesNE_of {d i ks ats} {xs : List EntityType} {n : Nat} (h : AppliesF d i ks ats xs)
    (hne : xs ≠ []) (hn : xs.length ≤ n) : AppliesNE d i ks ats n xs := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
  cases h
  case cons hx hxs =>
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
    exact .mk _ _ _ _ _ _ _ hx (appliesBounded_of hxs (by simp only [List.length_cons] at hn; omega))

theorem rawResources_of {d i ks ats} {b : Nat} {ps rs : List EntityType}
    (h : AppliesF d i ks ats rs) (hb : ps.length * rs.length ≤ b) :
    RawResources d i ks ats b ps rs := by
  cases ps with
  | nil => exact .none _ _ _ _ _ _ h
  | cons p ps =>
    refine .some _ _ _ _ _ _ _ _ (appliesBounded_of h ?_)
    rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
    simpa using hb

/-! ## Entities -/

/-- An entity entry, generated in any position (with the `free` rule for its parents). -/
def EntRow (m e d n i : Bool) (ks sks eks ats : List EntityType) : EntitySchemaEntry → Prop
  | .standard ⟨⟨ancs⟩, ⟨attrs⟩, tags⟩ =>
    (∀ seen seenStd, ParentsF .dense m d n ks sks eks seen seenStd ancs) ∧
      RecTyF m d i true ks ats attrs ∧ TagsF m d i ks ats tags
  | .enum ⟨eids⟩ => EidsF m e eids

theorem entsF_of_rows {m e d n i ks sks eks ats} :
    ∀ (ents : List (EntityType × EntitySchemaEntry)), (∀ p ∈ ents, EntRow m e d n i ks sks eks ats p.2) →
      ∀ seen seenStd, EntsF m e d n i .dense ks sks eks ats seen seenStd (kindsOf ents) ents
  | [], _, _, _ => .nil _ _
  | (x, .standard ⟨⟨ancs⟩, ⟨attrs⟩, tags⟩) :: ents, h, seen, seenStd => by
    obtain ⟨h₁, h₂, h₃⟩ := h _ List.mem_cons_self
    exact .std _ _ _ _ _ _ _ _ (h₁ _ _) h₂ h₃
      (entsF_of_rows ents (fun p hp => h p (List.mem_cons_of_mem _ hp)) _ _)
  | (x, .enum ⟨eids⟩) :: ents, h, seen, seenStd =>
    .enum _ _ _ _ _ _ (h _ List.mem_cons_self)
      (entsF_of_rows ents (fun p hp => h p (List.mem_cons_of_mem _ hp)) _ _)

/-! ## Actions -/

/-- An action entry, generated in any position with rank `k`. -/
def ActRow (m a d i : Bool) (r : HierMode) (ks ats : List EntityType) (uids : List EntityUID)
    (ranked : List (EntityUID × Nat)) (k : Nat) : ActionSchemaEntry → Prop
  | ⟨⟨ps⟩, ⟨rs⟩, ⟨ancs⟩, ⟨ctx⟩⟩ =>
    AppliesF d i ks ats ps ∧ SetArrET m ps ps ∧ AppliesF d i ks ats rs ∧ SetArrET m rs rs ∧
      AParents r m d a ranked k uids ancs ∧ RecTyF m d i d ks ats ctx

theorem actsB_of_rows {m a d i r ks ats uids ranked} (rk : EntityUID × ActionSchemaEntry → Nat) :
    ∀ (acts : List (EntityUID × ActionSchemaEntry)),
      (∀ p ∈ acts, ActRow m a d i r ks ats uids ranked (rk p) p.2) →
      ∀ b, envCount acts ≤ b →
        ActsB m a d i r ks ats uids ranked b (acts.map fun p => (p.1, rk p)) acts
  | [], _, _, _ => .nil _
  | (u, ⟨⟨ps⟩, ⟨rs⟩, ⟨ancs⟩, ⟨ctx⟩⟩) :: acts, h, b, hb => by
    obtain ⟨hp, hps, hr, hrs, ha, hc⟩ := h _ List.mem_cons_self
    rw [envCount_cons] at hb
    simp only at hb
    have hprod : ps.length * rs.length ≤ b := by
      change ps.length * rs.length + envCount acts ≤ b at hb; omega
    exact .cons _ _ _ _ ps rs ancs ctx _ (.mk _ _ _ _ _ _ ps hp hps)
      (.mk _ _ _ _ _ _ _ _ rs (rawResources_of hr hprod) hrs) ha hc
      (actsB_of_rows rk acts (fun p hp => h p (List.mem_cons_of_mem _ hp)) _
        (by change ps.length * rs.length + envCount acts ≤ b at hb; omega))

theorem envCount_pos_of_reqIn {acts : List (EntityUID × ActionSchemaEntry)} {reqty : RequestType}
    (h : ReqIn acts reqty) : 0 < envCount acts := by
  obtain ⟨e, he, hp, hr, -⟩ := h
  induction acts with
  | nil => cases he
  | cons q acts ih =>
    rw [envCount_cons]
    rcases List.mem_cons.mp he with rfl | he
    · have h₁ : 0 < e.appliesToPrincipal.toList.length := List.length_pos_iff_exists_mem.mpr ⟨_, hp⟩
      have h₂ : 0 < e.appliesToResource.toList.length := List.length_pos_iff_exists_mem.mpr ⟨_, hr⟩
      have := Nat.mul_pos h₁ h₂
      simp only
      omega
    · have := ih he; omega

theorem actsR_of_rows {m a d i r ks ats uids ranked} (rk : EntityUID × ActionSchemaEntry → Nat) :
    ∀ (acts : List (EntityUID × ActionSchemaEntry)),
      (∀ p ∈ acts, ActRow m a d i r ks ats uids ranked (rk p) p.2) →
      ∀ reqty, ReqIn acts reqty → ∀ b, envCount acts ≤ b →
        ActsR m a d i r ks ats uids ranked b (acts.map fun p => (p.1, rk p)) acts reqty
  | [], _, _, h, _, _ => absurd (envCount_pos_of_reqIn h) (by simp [envCount])
  | (u, ⟨⟨ps⟩, ⟨rs⟩, ⟨ancs⟩, ⟨ctx⟩⟩) :: acts, h, reqty, hreq, b, hb => by
    obtain ⟨hp, hps, hr, hrs, ha, hc⟩ := h _ List.mem_cons_self
    have hrows : ∀ p ∈ acts, ActRow m a d i r ks ats uids ranked (rk p) p.2 :=
      fun p hp => h p (List.mem_cons_of_mem _ hp)
    rw [envCount_cons] at hb
    change ps.length * rs.length + envCount acts ≤ b at hb
    obtain ⟨e', he', hpe, hre, hce⟩ := hreq
    by_cases hhead : (reqty.action, e') = (u, ⟨⟨ps⟩, ⟨rs⟩, ⟨ancs⟩, ⟨ctx⟩⟩)
    · -- the request's action
      simp only [Prod.mk.injEq] at hhead
      obtain ⟨hu, rfl⟩ := hhead
      obtain ⟨p, u', res, ctx'⟩ := reqty
      simp only at hu hpe hre hce
      subst hu hce
      have hpne : ps ≠ [] := List.ne_nil_of_mem hpe
      have hrne : rs ≠ [] := List.ne_nil_of_mem hre
      have hpl : 0 < ps.length := List.length_pos_iff.mpr hpne
      have hrl : 0 < rs.length := List.length_pos_iff.mpr hrne
      have hpb : ps.length ≤ b := Nat.le_trans (Nat.le_mul_of_pos_right _ hrl) (by omega)
      have hrb : rs.length ≤ b / ps.length := by
        rw [Nat.le_div_iff_mul_le hpl, Nat.mul_comm]; omega
      exact .request _ _ _ _ ps p rs res ancs ctx _
        (.mk _ _ _ _ _ _ _ ps (appliesNE_of hp hpne hpb) hps) (definedEntityType_iff_mem.mpr hpe)
        (.mk _ _ _ _ _ _ _ rs (appliesNE_of hr hrne hrb) hrs) (definedEntityType_iff_mem.mpr hre)
        ha hc (actsB_of_rows rk acts hrows _ (by omega))
    · -- an action before it
      have he' : (reqty.action, e') ∈ acts := by
        rcases List.mem_cons.mp he' with h | h
        · exact absurd h hhead
        · exact h
      have hreq' : ReqIn acts reqty := ⟨e', he', hpe, hre, hce⟩
      have hpos := envCount_pos_of_reqIn hreq'
      exact .cons _ _ _ _ ps rs ancs ctx _ _ (.mk _ _ _ _ _ _ ps hp hps)
        (.mk _ _ _ _ _ _ _ _ rs (rawResources_of hr (by omega)) hrs) ha hc
        (actsR_of_rows rk acts hrows reqty hreq' _ (by omega))

/-! ## Ranks -/

/-- The ancestors of the action `u` in `acts` (none if it is not declared). -/
def ancsOf (acts : List (EntityUID × ActionSchemaEntry)) (u : EntityUID) : List EntityUID :=
  (((Map.mk acts).find? u).map (·.ancestors.elts)).getD []

/-- An action's rank: how many of the actions are its ancestors. -/
def rankOf (acts : List (EntityUID × ActionSchemaEntry)) (u : EntityUID) : Nat :=
  ((acts.map Prod.fst).filter fun v => decide (v ∈ ancsOf acts u)).length

theorem length_filter_le {α} {P Q : α → Bool} : ∀ {l : List α},
    (∀ y ∈ l, P y = true → Q y = true) → (l.filter P).length ≤ (l.filter Q).length
  | [], _ => by simp
  | y :: l, h => by
    have ih := length_filter_le (P := P) (Q := Q) (l := l) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [List.filter_cons]
    by_cases hp : P y = true
    · simp [hp, h y List.mem_cons_self hp]; omega
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      split <;> simp <;> omega

theorem length_filter_lt {α} {P Q : α → Bool} : ∀ {l : List α} {x : α},
    (∀ y ∈ l, P y = true → Q y = true) → x ∈ l → Q x = true → P x = false →
      (l.filter P).length < (l.filter Q).length
  | [], _, _, h, _, _ => absurd h List.not_mem_nil
  | y :: l, x, h, hx, hq, hp => by
    have hle := length_filter_le (P := P) (Q := Q) (l := l) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [hp, hq]; omega
    · have ih := length_filter_lt (fun z hz => h z (List.mem_cons_of_mem _ hz)) hx hq hp
      by_cases hpy : P y = true
      · simp [hpy, h y List.mem_cons_self hpy]; omega
      · simp only [hpy, Bool.false_eq_true, ↓reduceIte]
        split <;> simp <;> omega

/-- In a transitive, irreflexive hierarchy, an ancestor has a lower rank. -/
theorem rank_lt {acts : List (EntityUID × ActionSchemaEntry)} (hnd : (acts.map Prod.fst).Nodup)
    (htr : ∀ p ∈ acts, ∀ q ∈ acts, q.1 ∈ p.2.ancestors.elts → ∀ x ∈ q.2.ancestors.elts,
      x ∈ p.2.ancestors.elts)
    (hirr : ∀ p ∈ acts, p.1 ∉ p.2.ancestors.elts)
    {u x : EntityUID} {e e' : ActionSchemaEntry} (hu : (u, e) ∈ acts) (hx : (x, e') ∈ acts)
    (hxu : x ∈ e.ancestors.elts) : rankOf acts x < rankOf acts u := by
  have hau : ancsOf acts u = e.ancestors.elts := by simp [ancsOf, find?_of_mem_nodup hnd hu]
  have hax : ancsOf acts x = e'.ancestors.elts := by simp [ancsOf, find?_of_mem_nodup hnd hx]
  unfold rankOf
  rw [hau, hax]
  refine length_filter_lt (x := x) ?_ (List.mem_map.mpr ⟨_, hx, rfl⟩) (by simpa using hxu)
    (by simpa using hirr _ hx)
  intro y _ hy
  simp only [decide_eq_true_eq] at hy ⊢
  exact htr _ hu _ hx hxu y hy

/-! ## Completeness for `typeOf`: every `EnvAssumptions` environment -/

theorem keyArrET_dedup {xs : List EntityType} (h : xs.Nodup) : KeyArrET false xs xs := by
  have := KeyArrET.dedupF xs; rwa [dedupKeep_of_nodup h] at this

theorem keyArrUID_dedup {xs : List EntityUID} (h : xs.Nodup) : KeyArrUID false xs xs := by
  have := KeyArrUID.dedupF xs; rwa [dedupKeep_of_nodup h] at this

/-- **Completeness for `typeOf`.** With every flag `false`, `GenTypeEnvF` generates every
environment satisfying `EnvAssumptions` with at most `budget` request environments (in the
`dense` mode). -/
theorem GenTypeEnvF.complete_envAssumptions {b : Nat} {env : TypeEnv} (h : EnvAssumptions env)
    (hb : env.schema.environments.length ≤ b) :
    GenTypeEnvF false false false false false false false .dense b env := by
  obtain ⟨⟨ents⟩, ⟨acts⟩, reqty⟩ := env
  rw [environments_length] at hb
  have hnd : (ents.map Prod.fst).Nodup := h.ets_keys_nodup
  have hndA : (acts.map Prod.fst).Nodup := h.acts_keys_nodup
  let sk : Skeleton := ⟨ents.map Prod.fst, kindsOf ents, stdOf ents, enumOf ents, acts.map Prod.fst,
    (acts.map Prod.fst).map (·.ty), acts.map fun p => (p.1, 0)⟩
  have hv : ∀ x, ValidEntityType x (Map.mk ents) (Map.mk acts) → x ∈ sk.ks ∨ x ∈ sk.ats :=
    fun x hx => mem_of_validEntityType hx
  have hsk : SkelF false false false sk :=
    .mk _ _ _ _ _ _ _ _ _ _ _ (.mk _ _ _ _ (rawNames_of fun _ _ => .any _) (keyArrET_dedup hnd))
      (kinds_kindsOf ents) (stdNames_kindsOf ents) (enumNames_kindsOf ents)
      (.mk _ _ _ _ _ _ _ _ (rawUids_of fun _ _ => .mk _ _ _ _ (.any _) (.lax _ _))
        (keyArrUID_dedup hndA) (typesOf_map _) (ranked_map (fun _ => 0) acts)) (.lax _ _)
  have hents : EntsAll false false false false false false .dense sk ents := by
    refine .mk ents ents (entsF_of_rows ents ?_ [] []) (.keep _ _)
    rintro ⟨x, entry⟩ hp
    have hf := find?_of_mem_nodup hnd hp
    cases entry with
    | standard se =>
      obtain ⟨⟨ancs⟩, ⟨attrs⟩, tags⟩ := se
      have hattrs : EntitySchema.attrs? (Map.mk ents) x = some ⟨attrs⟩ := by
        simp [EntitySchema.attrs?, hf, EntitySchemaEntry.attrs]
      refine ⟨fun _ _ => .freeF _ _ _ _ _ _ _ ancs ancs ?_ (.keepF _), ?_, ?_⟩
      · clear hp hf hattrs
        induction ancs with
        | nil => exact .nil _ _ _ _ _
        | cons y ys ih => exact .cons _ _ _ _ _ _ _ (.anyF _ _ _ _ _ (.laxF _ _)) ih
      · exact (tyF_of_tyWf hv (h.attrs_tyWf hattrs) (h.attrs_typeValid hattrs)).recTyF
      · cases tags with
        | none => exact .none
        | some ty =>
          have ht : EntitySchema.tags? (Map.mk ents) x = some (some ty) := by
            simp [EntitySchema.tags?, hf, EntitySchemaEntry.tags?]
          exact .some _ (tyF_of_tyWf hv (h.tags_tyWf ht) (h.tags_typeValid ht))
    | enum eids =>
      obtain ⟨l⟩ := eids
      refine .mk _ _ l l ?_ (.keepF _)
      cases l with
      | nil => exact .nilF
      | cons y ys => exact .consF _ _ (rawStrs_of ys)
  have hacts : ActsAllB false false false .dense sk b acts := by
    refine .mk acts acts (actsB_of_rows (fun _ => 0) acts ?_ b hb) (.keep _ _)
    rintro ⟨u, ⟨⟨ps⟩, ⟨rs⟩, ⟨ancs⟩, ⟨ctx⟩⟩⟩ _
    refine ⟨appliesF_of fun _ _ => .anyFF _ _ _, .keepF _, appliesF_of fun _ _ => .anyFF _ _ _,
      .keepF _, .freeF _ _ _ _ _ ancs ancs ?_ (.keepF _), (tyF_any (.record ⟨ctx⟩)).recTyF⟩
    clear * -
    induction ancs with
    | nil => exact .nil _ _ _ _ _
    | cons y ys ih =>
      refine .cons _ _ _ _ _ _ _ ?_ ih
      by_cases hy : y ∈ acts.map Prod.fst
      · exact .declF _ _ _ _ _ _ (.allF _ _ _) (definedUID_iff_mem.mpr hy)
      · obtain ⟨ty, eid⟩ := y
        exact .undeclF _ _ _ _ _ _ (notInUID_iff.mpr hy)
  have hreq : ReqFree false false sk.ks sk.ats reqty := by
    obtain ⟨p, ⟨ty, eid⟩, res, ⟨ctx⟩⟩ := reqty
    obtain ⟨hp, hr, hty, hctx⟩ := h.reqty_valid
    exact .mk _ _ _ _ _ _ _ _ _ (refIf_of_mem (hv _ hp)) (refIf_of_mem (hv _ hr))
      (refAny_of_mem (hv _ hty)) (tyF_of_tyWf hv h.context_tyWf hctx).recTyF
  exact .free _ _ _ _ _ _ _ _ ents acts reqty sk .dense hsk hents hacts hreq

/-! ## Completeness for `validateWellFormed`: every `TypeEnvWF` environment -/

theorem notInET_of_find?_none {ents : List (EntityType × EntitySchemaEntry)} {x : EntityType}
    (h : (Map.mk ents).find? x = none) : NotInET x (ents.map Prod.fst) := by
  refine notInET_iff.mpr fun hx => ?_
  obtain ⟨v, hv⟩ := mem_keys_iff.mp hx
  have := (map_contains_iff_mapContains (m := Map.mk ents)).mpr ⟨_, mem_toList_mapContains hv⟩
  obtain ⟨w, hw⟩ := Map.contains_iff_some_find?.mp this
  rw [h] at hw
  cases hw

theorem ancElems_decl {ks sks eks} : ∀ {l : List EntityType}, (∀ y ∈ l, y ∈ ks) →
    AncElems true false ks sks eks l
  | [], _ => .nil _ _ _ _ _
  | y :: ys, h => .cons _ _ _ _ _ _ _
      (.declT _ _ _ _ _ _ (.allF _ _) (definedEntityType_iff_mem.mpr (h y List.mem_cons_self)))
      (ancElems_decl fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem aElems_lower {ranked k uids} : ∀ {l : List EntityUID}, (∀ y ∈ l, y ∈ lowerOf ranked k) →
    AElems true true ranked k uids l
  | [], _ => .nil _ _ _ _ _
  | y :: ys, h => .cons _ _ _ _ _ _ _ (.declT _ _ _ _ _ _ (.lowerT _ _ _ _ (.mk _ _))
      (definedUID_iff_mem.mpr (h y List.mem_cons_self)))
      (aElems_lower fun z hz => h z (List.mem_cons_of_mem _ hz))

/-- **Completeness for `validateWellFormed`.** With the four `wf` flags, `GenTypeEnvF` generates
every `TypeEnvWF` environment with at most `budget` request environments (in the `dense`
mode). -/
theorem GenTypeEnvF.complete_typeEnvWF {b : Nat} {env : TypeEnv} (h : TypeEnvWF env)
    (hb : env.schema.environments.length ≤ b) :
    GenTypeEnvF true true true true false false false .dense b env := by
  obtain ⟨⟨ents⟩, ⟨acts⟩, reqty⟩ := env
  rw [environments_length] at hb
  cases h
  case mk hE hA hR =>
  cases hE
  case mk hEs hEe =>
  cases hA
  case mk hAs hAe hAcyc hTrans =>
  have hEe := entityEntriesWF_iff.mp hEe
  have hAe := actionEntriesWF_iff.mp hAe
  have hks : EltsSorted (ents.map Prod.fst) := map_fst_of_keysSorted hEs
  have huids : EltsSorted (acts.map Prod.fst) := map_fst_of_keysSorted hAs
  have hnd : (ents.map Prod.fst).Nodup := nodup_of_eltsSorted hks
  have hndA : (acts.map Prod.fst).Nodup := nodup_of_eltsSorted huids
  have hirr : ∀ p ∈ acts, p.1 ∉ p.2.ancestors.elts := by
    cases hAcyc; case mk h => exact actionsIrreflexive_iff.mp h
  have htr : ∀ p ∈ acts, ∀ q ∈ acts, q.1 ∈ p.2.ancestors.elts → ∀ x ∈ q.2.ancestors.elts,
      x ∈ p.2.ancestors.elts := by
    cases hTrans
    case mk h =>
      intro p hp q hq hqp x hx
      exact actionsTransitiveFrom_iff.mp (actionsTransitive_iff.mp h p hp) q hq hqp x hx
  let rk : EntityUID × ActionSchemaEntry → Nat := fun p => rankOf acts p.1
  let sk : Skeleton := ⟨ents.map Prod.fst, kindsOf ents, stdOf ents, enumOf ents, acts.map Prod.fst,
    (acts.map Prod.fst).map (·.ty), acts.map fun p => (p.1, rk p)⟩
  have hv : ∀ x, EntityTypeWF (Map.mk ents) (Map.mk acts) x → x ∈ sk.ks ∨ x ∈ sk.ats :=
    fun x hx => mem_of_entityTypeWF hx
  have hsk : SkelF true true false sk := by
    refine .mk _ _ _ _ _ _ _ _ _ _ _ (.mk _ _ _ _ (rawNames_of fun _ _ => .any _) (keyArrET_self hks))
      (kinds_kindsOf ents) (stdNames_kindsOf ents) (enumNames_kindsOf ents)
      (.mk _ _ _ _ _ _ _ _ (rawUids_of fun u hu => .mk _ _ _ _ (.any _) (.strict _ _ _ ?_))
        (keyArrUID_self huids) (typesOf_map _) (ranked_map rk acts)) (.lax _ _)
    obtain ⟨e, he⟩ := mem_keys_iff.mp hu
    exact notInET_of_find?_none (hAe _ he).1
  have hents : EntsAll true true true false false false .dense sk ents := by
    refine .mk ents ents (entsF_of_rows ents ?_ [] []) (.keep _ _)
    rintro ⟨x, entry⟩ hp
    have hwf := hEe _ hp
    cases entry with
    | standard se =>
      obtain ⟨⟨ancs⟩, ⟨attrs⟩, tags⟩ := se
      cases hwf
      case standard hs =>
      cases hs
      case mk hsorted hanc hattrs hlift htags =>
      have hanc := entityAncestorsWF_iff.mp hanc
      refine ⟨fun _ _ => .freeF _ _ _ _ _ _ _ ancs ancs ?_ (setArrET_self hsorted),
        (tyF_of_cedarTypeWF hv hattrs hlift).recTyF, ?_⟩
      · exact ancElems_decl fun y hy => by
          obtain ⟨v, hv⟩ := hanc y hy
          exact mem_keys_iff.mpr ⟨v, mem_of_find? hv⟩
      · cases htags
        case none => exact .none
        case some h₁ h₂ => exact .some _ (tyF_of_cedarTypeWF hv h₁ h₂)
    | enum eids =>
      obtain ⟨l⟩ := eids
      cases hwf
      case enum y ys hsorted =>
        exact .mk _ _ _ (y :: ys) (.consT _ _ (rawStrs_of ys)) (setArrStr_self hsorted)
  have hacts : ActsAllR true true false .dense sk b acts reqty := by
    have hclosedB : closedB actAncs acts = true := (closedB_iff actAncs acts).mpr htr
    have hirrB : irreflB actAncs acts = true := (irreflB_iff actAncs acts).mpr hirr
    have hclose := CloseActs.closeS true true acts
      (by rw [closeAll_of_closed actAncs actWith actWith_actAncs true acts hclosedB]; exact hclosedB)
      (by rw [closeAll_of_closed actAncs actWith actWith_actAncs true acts hclosedB]; exact hirrB)
    rw [closeAll_of_closed actAncs actWith actWith_actAncs true acts hclosedB] at hclose
    refine .mk acts reqty acts (actsR_of_rows rk acts ?_ reqty ?_ b hb) hclose
    · rintro ⟨u, ⟨⟨ps⟩, ⟨rs⟩, ⟨ancs⟩, ⟨ctx⟩⟩⟩ hp
      obtain ⟨-, hwf⟩ := hAe _ hp
      match hwf with
      | .mk _ _ _ _ _ _ hps hrs hancs hpt hrt hanc hctx hlift =>
      have hpt := entityTypesWF_iff.mp hpt
      have hrt := entityTypesWF_iff.mp hrt
      have hanc := actionAncestorsWF_iff.mp hanc
      refine ⟨appliesF_of fun y hy => refIf_of_mem (hv _ (hpt y hy)), setArrET_self hps,
        appliesF_of fun y hy => refIf_of_mem (hv _ (hrt y hy)), setArrET_self hrs,
        .freeT _ _ _ _ _ ancs ancs ?_ (setArrUID_self hancs),
        (tyF_of_cedarTypeWF hv hctx hlift).recTyF⟩
      have : ∀ y ∈ ancs, y ∈ lowerOf sk.ranked (rk (u, ⟨⟨ps⟩, ⟨rs⟩, ⟨ancs⟩, ⟨ctx⟩⟩)) := by
        intro y hy
        obtain ⟨e', he'⟩ := Map.contains_iff_some_find?.mp (hanc y hy)
        have hy' : (y, e') ∈ acts := mem_of_find? he'
        refine mem_lowerOf.mpr ⟨rk (y, e'), List.mem_map.mpr ⟨_, hy', rfl⟩, ?_⟩
        exact rank_lt hndA htr hirr hp hy' hy
      exact aElems_lower this
    · cases hR
      case mk ps rs ancs ctx hf hp hr =>
        exact ⟨_, mem_of_find? (mapFind_iff_find?.mp hf), setContains_mk_iff_mem.mp hp,
          setContains_mk_iff_mem.mp hr, rfl⟩
  exact .decl _ _ _ _ _ _ _ _ ents acts reqty sk .dense hsk hents hacts

end Cedar.Validation.Relational.SchemaGen
