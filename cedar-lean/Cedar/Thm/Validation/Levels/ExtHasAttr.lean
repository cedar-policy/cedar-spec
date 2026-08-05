import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.IfThenElse
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Slice
import Cedar.Thm.Validation.Levels.Basic
import Cedar.Thm.Validation.Levels.CheckLevel
import Cedar.Thm.Validation.Levels.ReachableChild
import Cedar.Thm.Validation.Levels.ChainCostStep
import Cedar.Thm.Validation.Levels.SliceHelpers
import Cedar.Thm.WellTyped.Expr.Typechecking

/-!
This file proves that level checking for `.extHasAttr` expressions is sound.

Key insight: with the split-budget design, the entity access level for the base
expression is `n - k` (where `k` = chain cost), and the chain gets budget `k`.
This ensures: depth(base) + chain_hops ≤ n, so all entities fit within slice
level `n + 1`.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

set_option maxHeartbeats 800000

/-! ## Core helper lemmas -/

/--
One step of hasAttrs.loop on an entity: if attrsOrEmpty agrees for uid between
two stores, and the recursive call gives the same result, then hasAttrs.loop
gives the same result.
-/
private theorem hasAttrs_loop_entity_step
  (uid : EntityUID) (a : Attr) (rest : List Attr) (entities slice : Entities)
  (hattrs : entities.attrsOrEmpty uid = slice.attrsOrEmpty uid)
  (ih : ∀ next, hasAttrs.loop next rest entities = hasAttrs.loop next rest slice) :
  hasAttrs.loop (.prim (.entityUID uid)) (a :: rest) entities =
  hasAttrs.loop (.prim (.entityUID uid)) (a :: rest) slice := by
  simp only [hasAttrs.loop, attrsOf]
  simp only [hattrs]
  split
  · split
    · rfl
    · exact ih _
  · rfl

/--
One-step chain decomposition: if `checkExtHasAttrChainTy env ty (a :: rest) k = true`
then there exists a `nextTy` such that the tail chain check holds.
-/
private theorem chain_step
  (a : Attr) (rest : List Attr) (env : TypeEnv) (ty : CedarType)
  (hchain : checkExtHasAttrChainTy env ty (a :: rest)
    (extHasAttrChainCostTy env ty (a :: rest)) = true) :
  ∃ nextTy : CedarType,
    checkExtHasAttrChainTy env nextTy rest
      (extHasAttrChainCostTy env nextTy rest) = true := by
  cases rest with
  | nil =>
    -- (a :: []) = [a], checkExtHasAttrChainTy returns true, cost is 0
    exact ⟨.int, by simp [checkExtHasAttrChainTy]⟩
  | cons b bs =>
    -- (a :: b :: bs): unfold definitions which now match the (a :: rest) pattern
    simp only [checkExtHasAttrChainTy, extHasAttrChainCostTy] at hchain
    cases ty with
    | entity ety =>
      cases h1 : env.ets.attrs? ety with
      | none => exact ⟨.int, by cases bs <;> simp [checkExtHasAttrChainTy]⟩
      | some rty =>
        simp only [h1] at hchain
        cases h2 : rty.find? a with
        | none => exact ⟨.int, by cases bs <;> simp [checkExtHasAttrChainTy]⟩
        | some qty =>
          simp only [h2] at hchain
          cases hty : qty.getType <;> simp only [hty] at hchain
          all_goals first
            | (rename_i nextEty
               simp only [gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq] at hchain
               have h := hchain.2
               have : 1 + extHasAttrChainCostTy env (.entity nextEty) (b :: bs) - 1 =
                   extHasAttrChainCostTy env (.entity nextEty) (b :: bs) := by omega
               rw [this] at h
               exact ⟨_, h⟩)
            | exact ⟨_, hchain⟩
    | record rty =>
      cases h2 : rty.find? a with
      | none => exact ⟨.int, by cases bs <;> simp [checkExtHasAttrChainTy]⟩
      | some qty =>
        simp only [h2] at hchain
        cases hty : qty.getType <;> simp only [hty] at hchain
        all_goals first
          | (rename_i nextEty
             simp only [gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq] at hchain
             have h := hchain.2
             have : 1 + extHasAttrChainCostTy env (.entity nextEty) (b :: bs) - 1 =
                 extHasAttrChainCostTy env (.entity nextEty) (b :: bs) := by omega
             rw [this] at h
             exact ⟨_, h⟩)
          | exact ⟨_, hchain⟩
    | _ =>
      exact ⟨.int, by cases bs <;> simp [checkExtHasAttrChainTy]⟩


/--
If `attrsOrEmpty` agrees for ALL entity UIDs between two stores, then
`hasAttrs.loop` gives the same result on both stores, regardless of the
starting value or chain structure.
-/
private theorem hasAttrs_loop_store_agree
  (v : Value) (attrs : List Attr) (es₁ es₂ : Entities)
  (hagree : ∀ uid, es₁.attrsOrEmpty uid = es₂.attrsOrEmpty uid) :
  hasAttrs.loop v attrs es₁ = hasAttrs.loop v attrs es₂ := by
  induction attrs generalizing v with
  | nil => simp [hasAttrs.loop]
  | cons a rest ih =>
    simp only [hasAttrs.loop]
    -- attrsOf v (fun uid => .ok (es.attrsOrEmpty uid)) is the same for both
    -- stores because hagree says attrsOrEmpty agrees for all UIDs.
    -- attrsOf only calls the function when v = .prim (.entityUID uid)
    have hattrsOf : attrsOf v (fun uid => .ok (es₁.attrsOrEmpty uid)) =
                    attrsOf v (fun uid => .ok (es₂.attrsOrEmpty uid)) := by
      cases v with
      | prim p =>
        cases p with
        | entityUID uid => simp [attrsOf, hagree uid]
        | _ => simp [attrsOf]
      | record _ => simp [attrsOf]
      | set _ => simp [attrsOf]
      | ext _ => simp [attrsOf]
    -- Now both sides have same attrsOf result. The whole expression is determined
    -- by attrsOf and the recursive call. Since attrsOf agrees, and the recursive
    -- call uses `ih`, we're done.
    -- Use congrArg on the continuation
    cases hres : attrsOf v (fun uid => Except.ok (es₂.attrsOrEmpty uid)) with
    | error => simp [hattrsOf, hres]
    | ok r =>
      simp only [hattrsOf, hres]
      cases r.find? a with
      | none => rfl
      | some next =>
        simp only []
        cases rest with
        | nil => rfl
        | cons b bs => exact ih _

/--
If `uid` is reachable at level `n+1`, then its `find?` agrees between
entities and the slice at level `n+1`.
-/
theorem reachable_implies_find_agree
  (entities : Entities) (request : Request) (uid : EntityUID) (n : Nat)
  (hr : ReachableIn entities request.sliceEUIDs uid (n + 1)) :
  (entities.sliceAtLevel request (n + 1)).find? uid = entities.find? uid := by
  cases hf : entities.find? uid with
  | none => exact not_entities_then_not_slice hf
  | some ed =>
    simp only [Entities.sliceAtLevel]
    have hi := slice_contains_reachable hr
    let eids := Entities.sliceAtLevel.sliceAtLevel entities request.sliceEUIDs (n + 1)
    let eds := eids.elts.filterMap (λ e => do some (e, ← Map.find? entities e))
    have hmake : Map.mk eds = Map.make eds := by
      have hsorted := eids.wf_iff_sorted.mp slice_at_level_inner_well_formed
      have hsbfst : eds.SortedBy Prod.fst := List.filterMap_key_id_sortedBy_key hsorted
      have hwf : (Map.mk eds).WellFormed := by
        simpa [Map.wf_iff_sorted] using hsbfst
      simpa [Map.WellFormed] using hwf
    rw [←hmake]
    exact (Map.find?_filterMap_key_id hi).symm ▸ hf

private def ExtHasAttrChainReachable
  (entities : Entities) (request : Request) (env : TypeEnv)
  (v : Value) (ty : CedarType) (attrs : List Attr) (sliceLevel : Nat) : Prop :=
  match ty with
  | .entity _ => ∀ uid, uid ∈ v.sliceEUIDs →
      ReachableIn entities request.sliceEUIDs uid
        (sliceLevel - extHasAttrChainCostTy env ty attrs)
  | .record _ => ∀ uid, uid ∈ v.sliceEUIDs →
      ReachableIn entities request.sliceEUIDs uid
        (sliceLevel - extHasAttrChainCostTy env ty attrs + 1)
  | _ => True

private theorem find?_slice_eq
  {entities : Entities} {request : Request} {uid : EntityUID}
  {level sliceLevel : Nat}
  (hr : ReachableIn entities request.sliceEUIDs uid level)
  (hle : level ≤ sliceLevel) (hpos : 0 < sliceLevel) :
  (entities.sliceAtLevel request sliceLevel).find? uid = entities.find? uid := by
  have hr' := reachable_of_le hr hle
  have heq : sliceLevel - 1 + 1 = sliceLevel := by omega
  rw [← heq] at hr' ⊢
  exact reachable_implies_find_agree entities request uid (sliceLevel - 1) hr'

private theorem hasAttrs_loop_chain_sound_strict
  {v : Value} {ty : CedarType} {attrs : List Attr} {sliceLevel : Nat}
  {entities : Entities} {request : Request} {env : TypeEnv}
  (hwf : InstanceOfWellFormedEnvironment request entities env)
  (hinst : InstanceOfType env v ty)
  (hchain : ExtHasAttrChainStrict env.ets ty attrs)
  (hcost : extHasAttrChainCostTy env ty attrs < sliceLevel)
  (hreach : ExtHasAttrChainReachable entities request env v ty attrs sliceLevel) :
  hasAttrs.loop v attrs entities =
    hasAttrs.loop v attrs (entities.sliceAtLevel request sliceLevel) := by
  induction hchain generalizing v with
  | last =>
    cases hinst with
    | instance_of_entity uid ety hity =>
      simp only [ExtHasAttrChainReachable] at hreach
      have hr := hreach uid (by simp [Value.sliceEUIDs, Set.mem_singleton])
      have hf := find?_slice_eq (sliceLevel := sliceLevel) hr (by omega) (by omega)
      simp [hasAttrs.loop, attrsOf, Entities.attrsOrEmpty, hf]
    | instance_of_record r rty h₁ h₂ h₃ => simp [hasAttrs.loop, attrsOf]
    | instance_of_bool | instance_of_int | instance_of_string |
      instance_of_set | instance_of_ext => simp [hasAttrs.loop, attrsOf]
  | cons_entity hschema htyfind hqty htail ih =>
    rename_i ety nextEty attr rest rty qty
    have ⟨uid, huidty, hv⟩ := instance_of_entity_type_is_entity hinst
    subst hv
    -- rest must be non-empty (from ExtHasAttrChainStrict); case-split to help simp unfold costTy
    cases rest with
    | nil => exact absurd htail (by intro h; cases h)
    | cons b bs =>
    simp [ExtHasAttrChainReachable, extHasAttrChainCostTy, hschema, htyfind, hqty] at hreach hcost
    have hr := hreach uid (by simp [Value.sliceEUIDs, Set.mem_singleton])
    have hf := find?_slice_eq (sliceLevel := sliceLevel) hr (by omega) (by omega)
    simp only [hasAttrs.loop, attrsOf]
    cases hed : entities.find? uid with
    | none =>
      have hs : (entities.sliceAtLevel request sliceLevel).find? uid = none := hf.trans hed
      simp [Entities.attrsOrEmpty, hed, hs]
    | some ed =>
      have hs : (entities.sliceAtLevel request sliceLevel).find? uid = some ed := hf.trans hed
      simp only [Entities.attrsOrEmpty, hed, hs]
      cases hfind : ed.attrs.find? _ with
      | none => simp
      | some next =>
        simp only []
        have hattrsinst := well_typed_entity_attributes hwf hed (by
          simpa [huidty] using hschema)
        have hnextinst := instance_of_attribute_type hattrsinst htyfind hqty hfind
        have ⟨uid2, huid2ty, hnext⟩ := instance_of_entity_type_is_entity hnextinst
        subst hnext
        split
        · rfl
        · apply ih hnextinst
          · omega
          · simp only [ExtHasAttrChainReachable]
            intro uid' hmem
            simp [Value.sliceEUIDs, Set.mem_singleton] at hmem
            subst uid'
            have hmemed : uid2 ∈ ed.sliceEUIDs :=
              sliceEUIDs_entity_attr hfind uid2 (by simp [Value.sliceEUIDs, Set.mem_singleton])
            have hpos : 0 < sliceLevel - (1 +
                extHasAttrChainCostTy env (.entity nextEty) (b :: bs)) := by omega
            have heq : sliceLevel - (1 +
                extHasAttrChainCostTy env (.entity nextEty) (b :: bs)) =
                (sliceLevel - (1 + extHasAttrChainCostTy env (.entity nextEty) (b :: bs)) - 1) + 1 := by omega
            have hc := reachable_child (heq ▸ hr) hed hmemed
            have htarget :
                (sliceLevel - (1 + extHasAttrChainCostTy env (.entity nextEty) (b :: bs)) - 1) + 2 =
                sliceLevel - extHasAttrChainCostTy env (.entity nextEty) (b :: bs) := by omega
            exact htarget ▸ hc
  | cons_record_from_entity hschema htyfind hqty htail ih =>
    rename_i ety attr rest rty qty recRty
    have ⟨uid, huidty, hv⟩ := instance_of_entity_type_is_entity hinst
    subst hv
    -- rest must be non-empty (from ExtHasAttrChainStrict); case-split to help simp unfold costTy
    cases rest with
    | nil => exact absurd htail (by intro h; cases h)
    | cons b bs =>
    simp [ExtHasAttrChainReachable, extHasAttrChainCostTy, hschema, htyfind, hqty] at hreach hcost
    have hr := hreach uid (by simp [Value.sliceEUIDs, Set.mem_singleton])
    have hf := find?_slice_eq (sliceLevel := sliceLevel) hr (by omega) (by omega)
    simp only [hasAttrs.loop, attrsOf]
    cases hed : entities.find? uid with
    | none =>
      have hs : (entities.sliceAtLevel request sliceLevel).find? uid = none := hf.trans hed
      simp [Entities.attrsOrEmpty, hed, hs]
    | some ed =>
      have hs : (entities.sliceAtLevel request sliceLevel).find? uid = some ed := hf.trans hed
      simp only [Entities.attrsOrEmpty, hed, hs]
      cases hfind : ed.attrs.find? _ with
      | none => simp
      | some next =>
        simp only []
        have hattrsinst := well_typed_entity_attributes hwf hed (by
          simpa [huidty] using hschema)
        have hnextinst := instance_of_attribute_type hattrsinst htyfind hqty hfind
        split
        · rfl
        · apply ih hnextinst
          · exact hcost
          · simp only [ExtHasAttrChainReachable]
            intro uid2 hmem
            have hmemed := sliceEUIDs_entity_attr hfind uid2 hmem
            have hpos : 0 < sliceLevel -
                extHasAttrChainCostTy env (.record recRty) (b :: bs) := by omega
            have heq : sliceLevel - extHasAttrChainCostTy env (.record recRty) (b :: bs) =
                (sliceLevel - extHasAttrChainCostTy env (.record recRty) (b :: bs) - 1) + 1 := by omega
            have hc := reachable_child (heq ▸ hr) hed hmemed
            have htarget :
                (sliceLevel - extHasAttrChainCostTy env (.record recRty) (b :: bs) - 1) + 2 =
                sliceLevel - extHasAttrChainCostTy env (.record recRty) (b :: bs) + 1 := by omega
            exact htarget ▸ hc
  | cons_entity_from_record htyfind hqty htail ih =>
    rename_i recRty attr rest qty nextEty
    have ⟨r, hv⟩ := instance_of_record_type_is_record hinst
    subst hv
    cases rest with
    | nil => exact absurd htail (by intro h; cases h)
    | cons b bs =>
    simp only [hasAttrs.loop, attrsOf]
    cases hfind : r.find? _ with
    | none => simp
    | some next =>
      simp only []
      have hnextinst := instance_of_attribute_type hinst htyfind hqty hfind
      have ⟨uid, huidty, hnext⟩ := instance_of_entity_type_is_entity hnextinst
      subst hnext
      split
      · rfl
      · apply ih hnextinst
        · simp [extHasAttrChainCostTy, htyfind, hqty] at hcost
          omega
        · simp only [ExtHasAttrChainReachable] at hreach ⊢
          intro uid' hmem
          simp [Value.sliceEUIDs, Set.mem_singleton] at hmem
          subst uid'
          have hm := hreach uid (sliceEUIDs_record_field hfind uid
            (by simp [Value.sliceEUIDs, Set.mem_singleton]))
          simp [extHasAttrChainCostTy, htyfind, hqty] at hcost hm
          have heq : sliceLevel - (1 + extHasAttrChainCostTy env (.entity nextEty) (b :: bs)) + 1 =
              sliceLevel - extHasAttrChainCostTy env (.entity nextEty) (b :: bs) := by omega
          exact heq ▸ hm
  | cons_record_from_record htyfind hqty htail ih =>
    rename_i recRty attr rest qty nextRecRty
    have ⟨r, hv⟩ := instance_of_record_type_is_record hinst
    subst hv
    cases rest with
    | nil => exact absurd htail (by intro h; cases h)
    | cons b bs =>
    simp only [hasAttrs.loop, attrsOf]
    cases hfind : r.find? _ with
    | none => simp
    | some next =>
      simp only []
      have hnextinst := instance_of_attribute_type hinst htyfind hqty hfind
      split
      · rfl
      · apply ih hnextinst
        · simpa [extHasAttrChainCostTy, htyfind, hqty] using hcost
        · simp only [ExtHasAttrChainReachable] at hreach ⊢
          intro uid hmem
          have hm := hreach uid (sliceEUIDs_record_field hfind uid hmem)
          simpa [extHasAttrChainCostTy, htyfind, hqty] using hm


private theorem hasAttrs_loop_record_chain_sound
  {v : Value} {rty : RecordType} {attrs : List Attr} {sliceLevel : Nat}
  {entities : Entities} {request : Request} {env : TypeEnv}
  (hwf : InstanceOfWellFormedEnvironment request entities env)
  (hinst : InstanceOfType env v (.record rty))
  (hchain : ExtHasAttrChainStrict env.ets (.record rty) attrs)
  (hcost : extHasAttrChainCostTy env (.record rty) attrs < sliceLevel)
  (hreach : ∀ path,
    extHasAttrFirstEntityPath? env (.record rty) attrs = some path →
    ∀ uid, Value.EuidViaPath v path uid →
      ReachableIn entities request.sliceEUIDs uid
        (sliceLevel - extHasAttrChainCostTy env (.record rty) attrs + 1)) :
  hasAttrs.loop v attrs entities =
    hasAttrs.loop v attrs (entities.sliceAtLevel request sliceLevel) := by
  induction attrs generalizing v rty with
  | nil => cases hchain
  | cons attr rest ih =>
    cases hchain with
    | last =>
      have ⟨r, hv⟩ := instance_of_record_type_is_record hinst
      subst hv
      simp [hasAttrs.loop, attrsOf]
    | cons_entity_from_record htyfind hqty htail =>
      rename_i qty nextEty
      have ⟨r, hv⟩ := instance_of_record_type_is_record hinst
      subst hv
      simp only [hasAttrs.loop, attrsOf]
      cases hfind : r.find? attr with
      | none => simp
      | some next =>
        simp only []
        have hnextinst := instance_of_attribute_type hinst htyfind hqty hfind
        have ⟨uid, huidty, hnext⟩ := instance_of_entity_type_is_entity hnextinst
        subst hnext
        cases rest with
        | nil => cases htail
        | cons b bs =>
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
          have hcosteq : extHasAttrChainCostTy env (.record rty) (attr :: b :: bs) =
              1 + extHasAttrChainCostTy env (.entity nextEty) (b :: bs) := by
            simp [extHasAttrChainCostTy, htyfind, hqty]
          apply hasAttrs_loop_chain_sound_strict hwf hnextinst htail
          · rw [hcosteq] at hcost
            omega
          · simp only [ExtHasAttrChainReachable]
            intro uid' hmem
            simp [Value.sliceEUIDs, Set.mem_singleton] at hmem
            subst uid'
            have hp : extHasAttrFirstEntityPath? env (.record rty) (attr :: b :: bs) =
                some [attr] := by
              simp [extHasAttrFirstEntityPath?, htyfind, hqty]
            have hr := hreach [attr] hp uid (.record hfind (.euid uid))
            rw [hcosteq] at hr
            have heq : sliceLevel - (1 + extHasAttrChainCostTy env (.entity nextEty) (b :: bs)) + 1 =
                sliceLevel - extHasAttrChainCostTy env (.entity nextEty) (b :: bs) := by omega
            exact heq ▸ hr
    | cons_record_from_record htyfind hqty htail =>
      rename_i qty nextRecRty
      have ⟨r, hv⟩ := instance_of_record_type_is_record hinst
      subst hv
      simp only [hasAttrs.loop, attrsOf]
      cases hfind : r.find? attr with
      | none => simp
      | some next =>
        simp only []
        have hnextinst := instance_of_attribute_type hinst htyfind hqty hfind
        cases rest with
        | nil => cases htail
        | cons b bs =>
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
          have hcosteq : extHasAttrChainCostTy env (.record rty) (attr :: b :: bs) =
              extHasAttrChainCostTy env (.record nextRecRty) (b :: bs) := by
            simp [extHasAttrChainCostTy, htyfind, hqty]
          apply ih hnextinst htail
          · rw [hcosteq] at hcost
            exact hcost
          · intro path hp uid hvpath
            have hr := hreach (attr :: path) (by
              simp [extHasAttrFirstEntityPath?, htyfind, hqty, hp]) uid (.record hfind hvpath)
            rw [hcosteq] at hr
            exact hr


/-! ## The main soundness theorem -/

theorem level_based_slicing_is_sound_ext_has_attr
  {e : Expr} {tx : TypedExpr} {a : Attr} {attrs : List Attr}
  {n : Nat} {c₀ c₁: Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf (e.extHasAttr a attrs) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ihe : TypedAtLevelIsSound e)
  : evaluate (.extHasAttr e a attrs) request entities = evaluate (.extHasAttr e a attrs) request (entities.sliceAtLevel request n)
:= by
  simp only [typeOf, bind, Except.bind] at ht
  generalize hte : typeOf e c₀ env = res_e at ht
  cases res_e with
  | error => simp at ht
  | ok val_e =>
    obtain ⟨ty₁, c₁'⟩ := val_e
    simp only at ht
    have hext_ok : ∃ res, typeOfExtHasAttr ty₁ e (a :: attrs) c₀ env = .ok res := by
      cases hext : typeOfExtHasAttr ty₁ e (a :: attrs) c₀ env with
      | error err => simp [hext] at ht
      | ok res => exact ⟨res, rfl⟩
    obtain ⟨extRes, hext⟩ := hext_ok
    have hstrict := typeOfExtHasAttr_implies_chain_strict hext
    have htx : tx = TypedExpr.extHasAttr ty₁ a attrs (.bool .anyBool) := by
      revert ht
      generalize typeOfExtHasAttr ty₁ e (a :: attrs) c₀ env = res_ext
      intro ht
      cases res_ext with
      | error => simp at ht
      | ok val_ext =>
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
        exact ht.1.symm
    rw [htx] at hl
    simp only [evaluate]
    cases hl with
    | extHasAttr _ _ _ _ _ hl₁ hty hchain hk =>
      -- Entity case: overall level = m + 1
      rename_i ety m
      have hl₁' : ty₁.AtLevel env (m + 1) := by
        apply entity_access_at_level_then_at_level (path := [])
        have bump : ∀ a b nmax path, a ≤ b →
            ty₁.EntityAccessAtLevel env a nmax path → ty₁.EntityAccessAtLevel env b nmax path := by
          intro a b nmax path hab h
          induction hab with
          | refl => exact h
          | step _ ih => exact entity_access_at_level_succ ih
        exact bump _ _ _ _ (Nat.sub_le _ _) hl₁
      have ihe_eq := ihe hc hr hte hl₁'
      rw [← ihe_eq]
      have ⟨ _, v, he, hv ⟩ := type_of_is_sound hc hr hte
      rw [hty] at hv
      have ⟨ euid, _, hv_eq ⟩ := instance_of_entity_type_is_entity hv
      subst hv_eq
      unfold EvaluatesTo at he
      rcases he with he | he | he | he <;> simp only [he, Except.bind_err, Except.bind_ok]
      simp only [hasAttrs]
      -- euid is reachable from checked_eval_entity_reachable
      have hreach_euid : ReachableIn entities request.sliceEUIDs euid
          (m - extHasAttrChainCost env ety (a :: attrs) + 1) :=
        checked_eval_entity_reachable hc hr hte hl₁ he (.euid euid)
      have hreach_eq : m - extHasAttrChainCost env ety (a :: attrs) + 1 =
          m + 1 - extHasAttrChainCost env ety (a :: attrs) := by omega
      apply hasAttrs_loop_chain_sound_strict hr hv (hstrict.1 ety hty)
      · simp only [extHasAttrChainCost] at hk ⊢
        omega
      · simp only [ExtHasAttrChainReachable]
        intro uid hmem
        simp [Value.sliceEUIDs, Set.mem_singleton] at hmem
        subst uid
        exact hreach_eq ▸ hreach_euid
    | extHasAttrRecord _ _ _ _ _ hl₁ hnotety hchain₁ =>
      rcases typeOfExtHasAttr_tyNext_type_entity_or_record hext with
        ⟨ety, hety⟩ | ⟨rty, hrty⟩
      · exact False.elim (hnotety ety hety)
      · have ihe_eq := ihe hc hr hte hl₁
        rw [← ihe_eq]
        have ⟨_, v, he, hv⟩ := type_of_is_sound hc hr hte
        rw [hrty] at hv
        unfold EvaluatesTo at he
        rcases he with he | he | he | he <;>
          simp only [he, Except.bind_err, Except.bind_ok]
        simp only [hasAttrs]
        have ⟨hcost, _, hpath⟩ := hchain₁ rty hrty
        apply hasAttrs_loop_record_chain_sound hr hv (hstrict.2 rty hrty) hcost
        intro path hp
        simp [hpath] at hp
    | extHasAttrRecordEntity _ _ _ _ _ rty path hl₁ hrty hcost _ hpath haccess =>
      have ihe_eq := ihe hc hr hte hl₁
      rw [← ihe_eq]
      have ⟨_, v, he, hv⟩ := type_of_is_sound hc hr hte
      rw [hrty] at hv
      unfold EvaluatesTo at he
      rcases he with he | he | he | he <;>
        simp only [he, Except.bind_err, Except.bind_ok]
      simp only [hasAttrs]
      apply hasAttrs_loop_record_chain_sound hr hv (hstrict.2 rty hrty) hcost
      intro path' hp uid hvpath
      have hpeq : path' = path := Option.some.inj (hp.symm.trans hpath)
      subst path'
      exact checked_eval_entity_reachable hc hr hte haccess he hvpath

end Cedar.Thm
