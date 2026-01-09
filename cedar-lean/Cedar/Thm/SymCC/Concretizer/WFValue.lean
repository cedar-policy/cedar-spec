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
import Cedar.Thm.SymCC.Data
import Cedar.Thm.Data.MapUnion
import Cedar.Thm.SymCC.Term.Same
import Cedar.Thm.SymCC.Term.WF

/-!
The lemmas in this file prove key properties of well-structured and
well-formed values.
-/

namespace Cedar.Thm
open Data Spec SymCC Factory

theorem value_set_entityUIDs_def {vs : Set Value} :
  (Value.set vs).entityUIDs = vs.elts.mapUnion Value.entityUIDs
:= by
  unfold Value.entityUIDs
  simp only [List.mapUnion₁_eq_mapUnion]

theorem value_record_entityUIDs_def {avs : Map Attr Value} :
  (Value.record avs).entityUIDs = avs.kvs.mapUnion λ (_, v) => v.entityUIDs
:= by
  rw [Value.entityUIDs]
  simp only [List.mapUnion₃_eq_mapUnion λ av : Attr × Value => av.snd.entityUIDs]

theorem value_ws_closed_implies_wf {v : Value} {es : Entities} :
  v.WellStructured →
  es.ClosedFor v.entityUIDs →
  v.WellFormed es
:= by
  intro hws hca
  induction hws
  case prim_ws =>
    apply Value.WellFormed.prim_wf
    simp only [Prim.WellFormed]
    split <;> try trivial
    rename_i uid
    simp only [Value.entityUIDs, Prim.entityUIDs] at hca
    exact hca uid (Set.mem_singleton uid)
  case set_ws h₂ ih =>
    apply Value.WellFormed.set_wf _ h₂
    intro v hv
    apply ih v hv
    intro uid huid
    apply hca uid
    simp only [value_set_entityUIDs_def]
    apply List.mem_mem_implies_mem_mapUnion huid
    exact (Set.in_list_iff_in_set _ _).mp hv
  case record_ws h₂ ih =>
    apply Value.WellFormed.record_wf _ h₂
    intro a v hf
    apply ih a v hf
    intro uid huid
    apply hca uid
    simp only [value_record_entityUIDs_def, List.mem_mapUnion_iff_mem_exists]
    exists (a, v)
    simp only [huid, and_true]
    exact Map.find?_mem_toList hf
  case ext_ws =>
    exact Value.WellFormed.ext_wf

theorem term_prim_value?_some_implies_ws {t : TermPrim} {v : Value} :
  t.value? = .some v → v.WellStructured
:= by
  intro hv
  simp only [TermPrim.value?, Option.pure_def, Option.bind_eq_bind] at hv
  cases t <;> simp only [Option.bind_eq_some_iff, Option.some.injEq] at hv
  all_goals {
    try (replace ⟨_, _, hv⟩ := hv)
    subst hv
    first
      | exact Value.WellStructured.prim_ws
      | exact Value.WellStructured.ext_ws
  }

theorem term_set_value?_some_implies {ts : List Term} {ty : TermType} {v : Value} :
  (Term.set (Set.mk ts) ty).value? = some v →
  ∃ vs,
    List.mapM Term.value? ts = some vs ∧ Value.set (Set.make vs) = v
:= by
  simp only [Term.value?, List.mapM₁_eq_mapM, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq, imp_self]

theorem term_set_value?_some_implies_ws {ts : List Term} {ty : TermType} {v : Value} {εs : SymEntities}
  (hw : Term.WellFormed εs (Term.set (Set.mk ts) ty))
  (hv : (Term.set (Set.mk ts) ty).value? = some v)
  (ih : ∀ (tᵢ : Term), tᵢ ∈ ts → ∀ {vᵢ : Value}, Term.WellFormed εs tᵢ → tᵢ.value? = some vᵢ → vᵢ.WellStructured) :
  v.WellStructured
:= by
  replace ⟨vs, hv, heq⟩ := term_set_value?_some_implies hv
  subst heq
  apply Value.WellStructured.set_ws _ (Set.make_wf _)
  intro vᵢ hin
  rw [← Set.make_mem] at hin
  replace ⟨tᵢ, hv⟩ := List.mapM_some_implies_all_from_some hv vᵢ hin
  replace hw := wf_term_set_implies_wf_elt hw hv.left
  exact ih tᵢ hv.left hw hv.right

private theorem term_record_value?_some_implies {ats : List (Attr × Term)} {v : Value} :
  (Term.record (Map.mk ats)).value? = .some v →
  ∃ avs,
    List.mapM (λ x => Term.value?.attrValue? x.fst x.snd) ats = some avs ∧
    Value.record (Map.mk (List.filterMap (λ x => Option.map (Prod.mk x.fst) x.snd) avs)) = v
:= by
  intro h
  simp only [Term.value?, List.mapM₂, List.attach₂,
    List.mapM_pmap_subtype (λ x : Attr × Term => Term.value?.attrValue? x.fst x.snd),
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  exact h

private theorem term_value?_attrValue?_some_implies_or {a : Attr} {t : Term} {v : Value} :
  Term.value?.attrValue? a t = some (a, some v) →
  t.value? = v ∨ ∃ t', t = .some t' ∧ t'.value? = v
:= by
  intro h
  replace h := value?_attrValue?_some_implies_same h
  simp only [same_values_def] at h
  split at h <;> simp only [h, or_true, true_or]

private theorem term_record_value?_sizeOf {a : Attr} {t : Term} {ats  : List (Attr × Term)} :
  sizeOf (a, t) < sizeOf ats → sizeOf (a, t).snd < (1 + sizeOf ats)
:= by
  simp only [Prod.mk.sizeOf_spec]
  omega

private theorem term_record_value?_sizeOf_some {a : Attr} {t : Term} {ats  : List (Attr × Term)} :
  sizeOf (a, Term.some t) < sizeOf ats → sizeOf (a, t).snd < (1 + sizeOf ats)
:= by
  simp only [Prod.mk.sizeOf_spec, Term.some.sizeOf_spec]
  omega

private theorem term_record_value?_some_implies_ws {ats : List (Attr × Term)} {v : Value} {εs : SymEntities}
  (hw : Term.WellFormed εs (Term.record (Map.mk ats)))
  (hv : (Term.record (Map.mk ats)).value? = some v)
  (ih : ∀ (aᵢ : Attr) (tᵢ : Term),
    sizeOf (aᵢ, tᵢ).snd < (1 + sizeOf ats) →
      Term.WellFormed εs tᵢ →
        ∀ (vᵢ : Value), tᵢ.value? = some vᵢ → vᵢ.WellStructured) :
  v.WellStructured
:= by
  replace ⟨avs, hm, hv⟩ := term_record_value?_some_implies hv
  subst hv
  apply Value.WellStructured.record_ws
  case h₁ =>
    intro a' v' hf
    replace hf := Map.find?_mem_toList hf
    simp only [Map.toList, Map.kvs, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq,
      exists_eq_right_right] at hf
    replace ⟨(aᵥ, vᵢ), hf, h₂, h₁⟩ := hf
    simp only at h₁ h₂ ; subst h₁ h₂
    replace ⟨(aₜ, tᵢ), hin, hm⟩ := List.mapM_some_implies_all_from_some hm (aᵥ, v') hf
    simp only at hm
    have ha := value?_attrValue?_fst hm
    simp only at ha ; subst ha
    replace hm := term_value?_attrValue?_some_implies_or hm
    replace hw := wf_term_record_implies_wf_value hw hin
    replace hin := List.sizeOf_lt_of_mem hin
    rcases hm with hm | hm
    case inl =>
      exact ih aₜ tᵢ (term_record_value?_sizeOf hin) hw _ hm
    case inr =>
      replace ⟨t', heq, hm⟩ := hm
      subst heq
      exact ih aₜ t' (term_record_value?_sizeOf_some hin) (wf_term_some_implies hw) _ hm
  case h₂ =>
    simp only [Map.wf_iff_sorted, Map.toList, Map.kvs]
    replace hw := wf_term_record_implies_wf_map hw
    simp only [Map.wf_iff_sorted, Map.toList, Map.kvs] at hw
    replace hm := List.mapM_some_eq_filterMap hm
    replace hw : avs.SortedBy Prod.fst := by
      rw [← hm]
      apply List.filterMap_sortedBy _ hw
      intro _ _ ha
      simp only [value?_attrValue?_fst ha]
    apply List.filterMap_sortedBy _ hw
    intro _ _ h
    simp only [Option.map] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    simp only [← h]

theorem term_value?_some_implies_ws {t : Term} {v : Value} {εs : SymEntities} :
  t.WellFormed εs → t.value? = .some v → v.WellStructured
:= by
  intro hw hv
  induction t using Term.value?.induct generalizing v
  case motive1 _ tᵢ =>
    exact (tᵢ.WellFormed εs → ∀ vᵢ, tᵢ.value? = .some vᵢ → vᵢ.WellStructured)
  case case1 | case2 =>
    simp only [Term.value?, false_implies, implies_true, reduceCtorEq]
  case case3 ih =>
    intro hw v hv
    exact ih hw hv
  case case4 =>
    simp only [Term.value?] at hv
    exact term_prim_value?_some_implies_ws hv
  case case5 ih =>
    exact term_set_value?_some_implies_ws hw hv ih
  case case6 ih =>
    exact term_record_value?_some_implies_ws hw hv ih
  case case7 =>
    simp only [Term.value?, reduceCtorEq] at hv

private theorem term_prim_value?_some_implies_eq_entityUIDs {t : TermPrim} {v : Value} :
  t.value? = some v → (Term.prim t).entityUIDs = v.entityUIDs
:= by
  intro hv
  simp only [TermPrim.value?, Option.pure_def, Option.bind_eq_bind] at hv
  cases t <;> simp only [Option.bind_eq_some_iff, Option.some.injEq] at hv
  all_goals {
    try (replace ⟨_, _, hv⟩ := hv)
    subst hv
    simp only [Term.entityUIDs, TermPrim.entityUIDs, Value.entityUIDs, Prim.entityUIDs]
  }

private theorem term_set_value?_some_implies_eq_entityUIDs {ts : List Term} {ty : TermType} {v : Value}
  (hv : (Term.set (Set.mk ts) ty).value? = some v)
  (ih : ∀ (tᵢ : Term), tᵢ ∈ ts →
    ∀ {vᵢ : Value}, tᵢ.value? = some vᵢ → tᵢ.entityUIDs = vᵢ.entityUIDs) :
  (Term.set (Set.mk ts) ty).entityUIDs = v.entityUIDs
:= by
  replace ⟨vs, hm, hv⟩ := term_set_value?_some_implies hv
  subst hv
  unfold Value.entityUIDs
  simp only [Term.entityUIDs, List.mapUnion₁_eq_mapUnion, Set.make]
  apply List.map_eqv_implies_mapUnion_eq
  simp only [List.Equiv, List.subset_def, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro tᵢ hin
    replace ⟨vᵢ, hin', hm⟩ := List.mapM_some_implies_all_some hm tᵢ hin
    exists vᵢ
    have h := (List.canonicalize_equiv vs).left
    simp only [List.subset_def] at h
    specialize h hin'
    replace hid : id = (fun x : Value => x) := by apply funext ; simp
    simp only [← hid, h, @ih tᵢ hin vᵢ hm, and_self]
  · intro vᵢ hin
    replace hin := List.in_canonicalize_in_list hin
    replace ⟨tᵢ, hin', hm⟩ := List.mapM_some_implies_all_from_some hm vᵢ hin
    exists tᵢ
    simp only [hin', @ih tᵢ hin' vᵢ hm, and_self]

private theorem term_record_value?_some_implies_eq_entityUIDs {ats : List (Attr × Term)} {v : Value}
  (hv : (Term.record (Map.mk ats)).value? = some v)
  (ih : ∀ (aᵢ : Attr) (tᵢ : Term),
    sizeOf (aᵢ, tᵢ).snd < (1 + sizeOf ats) →
    ∀ (vᵢ : Value), tᵢ.value? = some vᵢ → tᵢ.entityUIDs = vᵢ.entityUIDs) :
  (Term.record (Map.mk ats)).entityUIDs = v.entityUIDs
:= by
  replace ⟨avs, hm, hv⟩ := term_record_value?_some_implies hv
  subst hv
  simp only [Term.entityUIDs, Value.entityUIDs,
    ← List.mapM_some_eq_filterMap hm,
    List.mapUnion₃_eq_mapUnion (λ x : Attr × Term => x.snd.entityUIDs),
    List.mapUnion₃_eq_mapUnion (λ x : Attr × Value => x.snd.entityUIDs),
    List.filterMap_filterMap, List.mapUnion_filterMap]
  apply List.mapUnion_congr
  intro (aᵢ, tᵢ) hin
  replace ⟨(a', vopt), hm, hv⟩ := List.mapM_some_implies_all_some hm (aᵢ, tᵢ) hin
  simp only at hv
  have ha := value?_attrValue?_fst hv
  simp only at ha ; subst ha
  simp only [hv, Option.map, Option.bind_some]
  cases vopt
  case a.none =>
    simp only [Option.mapD_none]
    replace ⟨_, hv⟩ := value?_attrValue?_none_implies_none hv
    simp only [hv, Term.entityUIDs]
  case a.some vᵢ =>
    simp only [Option.mapD_some]
    replace hv := term_value?_attrValue?_some_implies_or hv
    rcases hv with hv | hv
    case inl =>
      apply ih aᵢ tᵢ _ _ hv
      exact term_record_value?_sizeOf (List.sizeOf_lt_of_mem hin)
    case inr =>
      replace ⟨t', heq, hv⟩ := hv
      subst heq
      simp only [Term.entityUIDs]
      apply ih aᵢ t' _ _ hv
      exact term_record_value?_sizeOf_some (List.sizeOf_lt_of_mem hin)

theorem term_value?_some_implies_eq_entityUIDs {t : Term} {v : Value} :
  t.value? = .some v → t.entityUIDs = v.entityUIDs
:= by
  intro hv
  induction t using Term.value?.induct generalizing v
  case motive1 _ tᵢ =>
    exact (∀ vᵢ, tᵢ.value? = .some vᵢ → tᵢ.entityUIDs = vᵢ.entityUIDs)
  case case1 | case2 =>
    simp only [Term.value?, false_implies, implies_true, reduceCtorEq]
  case case3 ih =>
    intro v hv
    exact ih hv
  case case4 =>
    simp only [Term.value?] at hv
    exact term_prim_value?_some_implies_eq_entityUIDs hv
  case case5 ih =>
    exact term_set_value?_some_implies_eq_entityUIDs hv ih
  case case6 ih =>
    exact term_record_value?_some_implies_eq_entityUIDs hv ih
  case case7 =>
    simp only [Term.value?, reduceCtorEq] at hv

end Cedar.Thm
