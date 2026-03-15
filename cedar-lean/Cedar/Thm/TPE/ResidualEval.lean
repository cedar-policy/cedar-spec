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

import Cedar.TPE.Residual
import Cedar.TPE.Evaluator
import Cedar.Thm.TPE.Input
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Control
import Cedar.Data.SizeOf

/-!
Evaluation lemmas for ResidualValue/Residual that don't depend on WellTyped.
Split out to avoid import cycles.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Data
open Cedar.TPE
open Cedar.Validation

@[simp]
theorem evaluate_asResidualValue (v : Value) (req : Request) (es : Entities) :
  (v.asResidualValue).evaluate req es = .ok v
:= by
  match v with
  | .prim p => simp [Value.asResidualValue, ResidualValue.evaluate]
  | .set s => simp [Value.asResidualValue, ResidualValue.evaluate]
  | .ext x => simp [Value.asResidualValue, ResidualValue.evaluate]
  | .record as =>
    simp only [Value.asResidualValue, Map.mapOnValues₂_eq_mapOnValues as (fun x => ResidualAttribute.present x.asResidualValue)]
    rw [ResidualValue.evaluate.eq_def]; dsimp only []
    rw [Map.mapMKVsIntoValues₂_eq_mapMKVsIntoValues _ (fun kv => ResidualValue.evaluateAttr kv req es)]
    rw [Map.mapMKVsIntoValues_mapOnValues_roundtrip
      (fun x => ResidualAttribute.present x.asResidualValue)
      (fun kv => ResidualValue.evaluateAttr kv req es)
      as
      (fun ⟨k, v⟩ hkv => by
        simp only [ResidualValue.evaluateAttr]
        exact evaluate_asResidualValue v req es)]
    rfl
termination_by sizeOf v
decreasing_by
  simp_wf
  have h1 := Map.sizeOf_lt_of_values (Map.in_list_in_values hkv)
  simp [Value.record.sizeOf_spec]; omega

theorem asResidualValue_evaluate {r : Residual} {rv : ResidualValue} :
  r.asResidualValue = some rv → ∀ req es, r.evaluate req es = rv.evaluate req es
:= by
  intro h req es
  cases r <;> simp [Residual.asResidualValue] at h
  subst h; simp [Residual.evaluate]


@[simp]
theorem someOrError_evaluate_ok {v : Value} {ty : CedarType} {req : Request} {es : Entities} :
  (someOrError (some v) ty).evaluate req es = Except.ok v := by
  simp [someOrError, Residual.evaluate, evaluate_asResidualValue]


@[simp]
theorem someOrError_evaluate_err {ty : CedarType} {req : Request} {es : Entities} :
  (someOrError none ty).evaluate req es = Except.error Error.extensionError := by
  simp [someOrError, Residual.evaluate]


@[simp]
theorem someOrSelf_some_evaluate {v : Value} {ty : CedarType} {r : Residual} {req : Request} {es : Entities} :
  (someOrSelf (some v) ty r).evaluate req es = Except.ok v := by
  simp [someOrSelf, Residual.evaluate, evaluate_asResidualValue]

@[simp] theorem Residual.typeOf_val {rv : ResidualValue} {ty : CedarType} :
  (Residual.val rv ty).typeOf = ty := rfl

@[simp] theorem Residual.typeOf_error {ty : CedarType} :
  (Residual.error ty).typeOf = ty := rfl

@[simp] theorem Residual.asResidualValue_val {rv : ResidualValue} {ty : CedarType} :
  (Residual.val rv ty).asResidualValue = some rv := by
  simp [Residual.asResidualValue]

@[simp] theorem Residual.asResidualValue_error {ty : CedarType} :
  (Residual.error ty).asResidualValue = none := by
  simp [Residual.asResidualValue]

/-! ## Core @[simp] lemmas for Residual.evaluate and ResidualValue.evaluate -/

@[simp] theorem Residual.evaluate_error {ty : CedarType} {req : Request} {es : Entities} :
  (Residual.error ty).evaluate req es = .error .extensionError := by
  unfold Residual.evaluate; rfl

@[simp] theorem Residual.evaluate_val {rv : ResidualValue} {ty : CedarType} {req : Request} {es : Entities} :
  (Residual.val rv ty).evaluate req es = rv.evaluate req es := by
  unfold Residual.evaluate; rfl

-- Key lemma: Residual.evaluate for getAttr/hasAttr in do-notation form
-- These bridge the gap between >>= notation and do notation
@[simp] theorem Except.bind_toOption {e : Except ε α} {f : α → Except ε β} :
  (e >>= f).toOption = (do let x ← e; f x).toOption := rfl

@[simp] theorem Except.do_eq_bind {e : Except ε α} {f : α → Except ε β} :
  (do let x ← e; f x) = (e >>= f) := rfl

-- Helper: mapMKVsIntoValues preserves find? relationships
-- We prove this via a list-level lemma about mapM preserving find?

-- Helper: decompose a successful mapM on cons
private theorem list_mapM_cons_ok
  {g : α → Except ε β}
  {hd : α} {tl : List α} {result : List β}
  (h : (hd :: tl).mapM g = .ok result) :
  ∃ hd' tl', result = hd' :: tl' ∧ g hd = .ok hd' ∧ tl.mapM g = .ok tl' := by
  simp only [List.mapM_cons, bind_pure_comp] at h
  cases hg : g hd with
  | error e => simp [hg, Functor.map, Except.map] at h
  | ok hd' =>
    cases htl : tl.mapM g with
    | error e => simp [hg, htl, Functor.map, Except.map] at h
    | ok tl' =>
      simp [hg, htl] at h
      exact ⟨hd', tl', h.symm, rfl, rfl⟩

private theorem list_mapM_find_some
  {f : α × β → Except ε γ}
  {kvs : List (α × β)} {kvs' : List (α × γ)}
  {k : α} {v : β} {w : γ} [BEq α]
  (hmap : kvs.mapM (fun kv => f kv >>= fun v' => pure (kv.fst, v')) = .ok kvs')
  (hfind : kvs.find? (fun ⟨k', _⟩ => k' == k) = some (k, v))
  (hf : f (k, v) = .ok w) :
  kvs'.find? (fun ⟨k', _⟩ => k' == k) = some (k, w) := by
  induction kvs generalizing kvs' with
  | nil => simp at hfind
  | cons hd tl ih =>
    obtain ⟨hd', tl', rfl, hhd', htl'⟩ := list_mapM_cons_ok hmap
    simp only [List.find?_cons] at hfind ⊢
    split at hfind
    · rename_i heq
      obtain ⟨rfl, rfl⟩ := by simpa using hfind
      simp only [hf, Except.bind_ok, pure, Except.pure, Except.ok.injEq] at hhd'
      subst hhd'; simp [heq]
    · rename_i hneq
      have hkey : hd'.fst = hd.fst := by
        have h := hhd'
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        split at h
        · simp at h
        · grind
      rw [hkey]; simp only [hneq, ↓reduceIte]
      exact ih htl' hfind

private theorem list_mapM_find_none
  {f : α × β → Except ε γ}
  {kvs : List (α × β)} {kvs' : List (α × γ)}
  {k : α} [BEq α]
  (hmap : kvs.mapM (fun kv => f kv >>= fun v' => pure (kv.fst, v')) = .ok kvs')
  (hfind : kvs.find? (fun ⟨k', _⟩ => k' == k) = none) :
  kvs'.find? (fun ⟨k', _⟩ => k' == k) = none := by
  induction kvs generalizing kvs' with
  | nil =>
    have : kvs' = [] := by simpa [pure, Except.pure] using hmap
    subst this; rfl
  | cons hd tl ih =>
    obtain ⟨hd', tl', rfl, hhd', htl'⟩ := list_mapM_cons_ok hmap
    simp only [List.find?_cons] at hfind ⊢
    split at hfind
    · simp at hfind
    · rename_i hneq
      have hkey : hd'.fst = hd.fst := by
        have h := hhd'
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        split at h
        · simp at h
        · grind
      rw [hkey]; simp only [hneq, ↓reduceIte]
      exact ih htl' hfind

-- Bridge: mapMKVsIntoValues produces Map.mk of the list-level mapM result
private theorem mapMKVsIntoValues_toList
  {f : Attr × β → Except ε γ} {m : Map Attr β} {result : Map Attr γ}
  (hmap : m.mapMKVsIntoValues f = .ok result) :
  m.toList.mapM (fun kv => f kv >>= fun v' => pure (kv.fst, v')) = .ok result.toList := by
  -- mapMKVsIntoValues is definitionally: mapM g >>= fun kvs => .ok (Map.mk kvs)
  -- where g kv = f kv >>= fun v' => pure (kv.fst, v')
  -- So if it = .ok result, then mapM g = .ok result.toList
  let g := fun kv : Attr × β => f kv >>= fun v' => pure (kv.fst, v')
  -- hmap is definitionally: (m.toList.mapM g >>= fun kvs => .ok (Map.mk kvs)) = .ok result
  change (m.toList.mapM g >>= fun kvs => .ok (Map.mk kvs)) = .ok result at hmap
  cases hm : m.toList.mapM g with
  | error e => simp [hm, Bind.bind, Except.bind] at hmap
  | ok kvs =>
    simp only [hm, Bind.bind, Except.bind, Except.ok.injEq] at hmap
    subst hmap; rfl

private theorem map_find_to_list_find
  {m : Map Attr β} {k : Attr} {v : β}
  (h : m.find? k = some v) :
  m.toList.find? (fun x => x.fst == k) = some (k, v) := by
  simp only [Map.find?] at h
  cases hf : m.toList.find? (fun x => x.fst == k) with
  | none => simp [hf] at h
  | some kv =>
    simp only [hf] at h
    have hpred := List.find?_some hf
    simp only at hpred
    have hk' : kv.fst = k := beq_iff_eq.mp hpred
    have hv' : kv.snd = v := by simpa using h
    rw [show kv = (k, v) from Prod.ext hk' hv']

private theorem map_find_none_to_list_find_none
  {m : Map Attr β} {k : Attr}
  (h : m.find? k = none) :
  m.toList.find? (fun x => x.fst == k) = none := by
  simp only [Map.find?] at h
  cases hf : m.toList.find? (fun x => x.fst == k) with
  | none => rfl
  | some kv => simp [hf] at h

private theorem mapMKVsIntoValues_find_some
  {f : Attr × β → Except ε γ} {m : Map Attr β} {result : Map Attr γ}
  {k : Attr} {v : β} {w : γ}
  (hmap : m.mapMKVsIntoValues f = .ok result)
  (hfind : m.find? k = some v)
  (hf : f (k, v) = .ok w) :
  result.find? k = some w := by
  have hlist := mapMKVsIntoValues_toList hmap
  have hfind_list := map_find_to_list_find hfind
  have hresult := list_mapM_find_some hlist hfind_list hf
  -- hresult : result.toList.find? (fun x => x.fst == k) = some (k, w)
  -- goal : result.find? k = some w
  -- result.find? k unfolds to: match result.toList.find? (fun x => x.fst == k) with | some (_, v) => some v | _ => none
  unfold Map.find?
  rw [hresult]

private theorem mapMKVsIntoValues_find_none
  {f : Attr × β → Except ε γ} {m : Map Attr β} {result : Map Attr γ}
  {k : Attr}
  (hmap : m.mapMKVsIntoValues f = .ok result)
  (hfind : m.find? k = none) :
  result.find? k = none := by
  have hlist := mapMKVsIntoValues_toList hmap
  have hfind_list := map_find_none_to_list_find_none hfind
  have hresult := list_mapM_find_none hlist hfind_list
  unfold Map.find?
  rw [hresult]

-- If mapMKVsIntoValues succeeds, then f succeeds on every element
private theorem list_mapM_elem_ok
  {g : α → Except ε β} {kvs : List α} {result : List β} {x : α}
  (hmap : kvs.mapM g = .ok result) (hmem : x ∈ kvs) :
  ∃ y, g x = .ok y := by
  induction kvs generalizing result with
  | nil => simp at hmem
  | cons hd tl ih =>
    obtain ⟨hd', tl', rfl, hhd', htl'⟩ := list_mapM_cons_ok hmap
    cases hmem with
    | head => exact ⟨hd', hhd'⟩
    | tail _ hmem => exact ih htl' hmem

private theorem mapMKVsIntoValues_elem_ok
  {f : Attr × β → Except ε γ} {m : Map Attr β} {result : Map Attr γ}
  {k : Attr} {v : β}
  (hmap : m.mapMKVsIntoValues f = .ok result)
  (hfind : m.find? k = some v) :
  ∃ w, f (k, v) = .ok w := by
  have hlist := mapMKVsIntoValues_toList hmap
  have hfind_list := map_find_to_list_find hfind
  -- (k, v) ∈ m.toList because find? found it
  have hmem : (k, v) ∈ m.toList := List.mem_of_find?_eq_some hfind_list
  -- The composed function g kv = f kv >>= fun v' => pure (kv.fst, v') succeeds on (k, v)
  have ⟨kv', hkv'⟩ := list_mapM_elem_ok hlist hmem
  -- kv' = (k, f(k,v).get), so f (k, v) must be .ok _
  simp only [Bind.bind, Except.bind, pure, Except.pure] at hkv'
  cases hf : f (k, v) with
  | error e => simp [hf] at hkv'
  | ok w => exact ⟨w, rfl⟩

-- Helper: extract the map from a successful record evaluation
private theorem record_evaluate_eq_mapM
  {m : Map Attr ResidualAttribute} {req : Request} {es : Entities} {v_rec : Value}
  (heval : (ResidualValue.record m).evaluate req es = .ok v_rec) :
  ∃ kvs, m.mapMKVsIntoValues₂ (fun ⟨kv, _⟩ => ResidualValue.evaluateAttr kv req es) = .ok kvs ∧
         v_rec = .record kvs := by
  simp only [ResidualValue.evaluate] at heval
  cases hm : m.mapMKVsIntoValues₂ (fun ⟨kv, _⟩ => ResidualValue.evaluateAttr kv req es) with
  | error => simp [hm] at heval
  | ok kvs => simp [hm] at heval; exact ⟨kvs, rfl, heval.symm⟩

/-- When a record ResidualValue evaluates successfully, getAttr on the result
    agrees with evaluating the individual attribute. -/
theorem record_evaluate_getAttr_present
  {m : Map Attr ResidualAttribute} {attr : Attr} {pv : ResidualValue}
  {req : Request} {es : Entities} {v_rec : Value}
  (heval : (ResidualValue.record m).evaluate req es = .ok v_rec)
  (hfind : m.find? attr = some (.present pv)) :
  Spec.getAttr v_rec attr es = pv.evaluate req es := by
  obtain ⟨kvs, hkvs, rfl⟩ := record_evaluate_eq_mapM heval
  have hkvs' : m.mapMKVsIntoValues (fun kv => ResidualValue.evaluateAttr kv req es) = .ok kvs := by
    rw [← Map.mapMKVsIntoValues₂_eq_mapMKVsIntoValues]; exact hkvs
  simp only [Spec.getAttr, Spec.attrsOf, Except.bind_ok]
  -- evaluateAttr (attr, .present pv) = pv.evaluate, and it must succeed
  have ⟨w, hw⟩ := mapMKVsIntoValues_elem_ok hkvs' hfind
  have hpv : pv.evaluate req es = .ok w := by unfold ResidualValue.evaluateAttr at hw; exact hw
  have hfind' := mapMKVsIntoValues_find_some hkvs' hfind hw
  simp [Data.Map.findOrErr, hfind', hpv]

theorem record_evaluate_getAttr_unknown
  {m : Map Attr ResidualAttribute} {attr : Attr} {tgt : Residual} {ty' : CedarType}
  {req : Request} {es : Entities} {v_rec : Value}
  (heval : (ResidualValue.record m).evaluate req es = .ok v_rec)
  (hfind : m.find? attr = some (.unknown tgt ty')) :
  Spec.getAttr v_rec attr es = (Residual.getAttr tgt attr ty').evaluate req es := by
  obtain ⟨kvs, hkvs, rfl⟩ := record_evaluate_eq_mapM heval
  have hkvs' : m.mapMKVsIntoValues (fun kv => ResidualValue.evaluateAttr kv req es) = .ok kvs := by
    rw [← Map.mapMKVsIntoValues₂_eq_mapMKVsIntoValues]; exact hkvs
  simp only [Spec.getAttr, Spec.attrsOf, Except.bind_ok]
  have ⟨w, hw⟩ := mapMKVsIntoValues_elem_ok hkvs' hfind
  have htgt : (Residual.getAttr tgt attr ty').evaluate req es = .ok w := by
    unfold ResidualValue.evaluateAttr at hw; exact hw
  have hfind' := mapMKVsIntoValues_find_some hkvs' hfind hw
  simp [Data.Map.findOrErr, hfind', htgt]

theorem record_evaluate_hasAttr_present
  {m : Map Attr ResidualAttribute} {attr : Attr} {pv : ResidualValue}
  {req : Request} {es : Entities} {v_rec : Value}
  (heval : (ResidualValue.record m).evaluate req es = .ok v_rec)
  (hfind : m.find? attr = some (.present pv)) :
  Spec.hasAttr v_rec attr es = .ok true := by
  obtain ⟨kvs, hkvs, rfl⟩ := record_evaluate_eq_mapM heval
  have hkvs' : m.mapMKVsIntoValues (fun kv => ResidualValue.evaluateAttr kv req es) = .ok kvs := by
    rw [← Map.mapMKVsIntoValues₂_eq_mapMKVsIntoValues]; exact hkvs
  have ⟨w, hw⟩ := mapMKVsIntoValues_elem_ok hkvs' hfind
  have hfind' := mapMKVsIntoValues_find_some hkvs' hfind hw
  simp [Spec.hasAttr, Spec.attrsOf, Map.contains, hfind']

theorem record_evaluate_hasAttr_unknown
  {m : Map Attr ResidualAttribute} {attr : Attr} {tgt : Residual} {ty' : CedarType}
  {req : Request} {es : Entities} {v_rec : Value}
  (heval : (ResidualValue.record m).evaluate req es = .ok v_rec)
  (hfind : m.find? attr = some (.unknown tgt ty')) :
  Spec.hasAttr v_rec attr es = (Residual.hasAttr tgt attr ty').evaluate req es := by
  obtain ⟨kvs, hkvs, rfl⟩ := record_evaluate_eq_mapM heval
  have hkvs' : m.mapMKVsIntoValues (fun kv => ResidualValue.evaluateAttr kv req es) = .ok kvs := by
    rw [← Map.mapMKVsIntoValues₂_eq_mapMKVsIntoValues]; exact hkvs
  -- LHS: hasAttr (.record kvs) attr es = .ok true (attr exists in kvs)
  have ⟨w, hw⟩ := mapMKVsIntoValues_elem_ok hkvs' hfind
  have hfind' := mapMKVsIntoValues_find_some hkvs' hfind hw
  have lhs : Spec.hasAttr (.record kvs) attr es = .ok true := by
    simp [Spec.hasAttr, Spec.attrsOf, Map.contains, hfind']
  -- RHS: (Residual.hasAttr tgt attr ty').evaluate = tgt.evaluate >>= hasAttr
  -- hw : evaluateAttr (attr, .unknown tgt ty') = .ok w
  -- evaluateAttr (attr, .unknown tgt ty') = (Residual.getAttr tgt attr ty').evaluate
  have hgetattr : (Residual.getAttr tgt attr ty').evaluate req es = .ok w := by
    unfold ResidualValue.evaluateAttr at hw; exact hw
  -- getAttr = tgt.evaluate >>= fun v => Spec.getAttr v attr es = .ok w
  -- So tgt.evaluate = .ok v_tgt for some v_tgt, and Spec.getAttr v_tgt attr es = .ok w
  unfold Residual.evaluate at hgetattr
  cases htgt : tgt.evaluate req es with
  | error e => simp [htgt] at hgetattr
  | ok v_tgt =>
    simp [htgt] at hgetattr
    -- hgetattr : Spec.getAttr v_tgt attr es = .ok w
    -- hasAttr succeeds when getAttr succeeds
    unfold Residual.evaluate; simp only [htgt, Bind.bind, Except.bind]
    rw [lhs]
    -- Need: .ok true = Spec.hasAttr v_tgt attr es
    -- We know Spec.getAttr v_tgt attr es = .ok w
    -- getAttr uses attrsOf v_tgt es.attrs, hasAttr uses attrsOf v_tgt (fun uid => .ok (es.attrsOrEmpty uid))
    -- For records: both return .ok r
    -- For entities: if es.attrs uid = .ok attrs, then es.attrsOrEmpty uid = attrs
    simp only [Spec.getAttr] at hgetattr
    simp only [Spec.hasAttr]
    cases v_tgt with
    | record r =>
      simp only [Spec.attrsOf] at hgetattr ⊢
      simp only [Except.bind_ok] at hgetattr ⊢
      simp only [Data.Map.findOrErr] at hgetattr
      split at hgetattr
      · simp [Map.contains, *]
      · simp at hgetattr
    | prim p =>
      cases p with
      | entityUID uid =>
        simp only [Spec.attrsOf] at hgetattr ⊢
        cases hea : es.attrs uid with
        | error e => simp [hea] at hgetattr
        | ok attrs =>
          simp only [hea, Except.bind_ok] at hgetattr
          -- es.attrsOrEmpty uid = attrs when es.attrs uid = .ok attrs
          have : es.attrsOrEmpty uid = attrs := by
            simp only [Entities.attrsOrEmpty, Entities.attrs, Data.Map.findOrErr] at hea ⊢
            split at hea
            · simp at hea; split <;> simp_all
            · simp at hea
          simp only [this, Except.bind_ok]
          simp only [Data.Map.findOrErr] at hgetattr
          split at hgetattr
          · simp [Map.contains, *]
          · simp at hgetattr
      | _ => simp [Spec.attrsOf] at hgetattr
    | _ => simp [Spec.attrsOf] at hgetattr

theorem record_evaluate_hasAttr_none
  {m : Map Attr ResidualAttribute} {attr : Attr}
  {req : Request} {es : Entities} {v_rec : Value}
  (heval : (ResidualValue.record m).evaluate req es = .ok v_rec)
  (hfind : m.find? attr = none) :
  Spec.hasAttr v_rec attr es = .ok false := by
  obtain ⟨kvs, hkvs, rfl⟩ := record_evaluate_eq_mapM heval
  have hkvs' : m.mapMKVsIntoValues (fun kv => ResidualValue.evaluateAttr kv req es) = .ok kvs := by
    rw [← Map.mapMKVsIntoValues₂_eq_mapMKVsIntoValues]; exact hkvs
  simp only [Spec.hasAttr, Spec.attrsOf, Except.bind_ok]
  have hfind' := mapMKVsIntoValues_find_none hkvs' hfind
  simp [Map.contains, hfind']

@[simp] theorem Residual.evaluate_getAttr {r : Residual} {a : Attr} {ty : CedarType} {req : Request} {es : Entities} :
  (Residual.getAttr r a ty).evaluate req es = (r.evaluate req es >>= fun v => Spec.getAttr v a es) := by
  simp only [Residual.evaluate, Bind.bind, Except.bind]

@[simp] theorem Residual.evaluate_hasAttr {r : Residual} {a : Attr} {ty : CedarType} {req : Request} {es : Entities} :
  (Residual.hasAttr r a ty).evaluate req es = (r.evaluate req es >>= fun v => Spec.hasAttr v a es) := by
  simp only [Residual.evaluate, Bind.bind, Except.bind]

/-- Soundness of getAttr when both sides are residual (non-value) -/
theorem getAttr_sound_of_sound {x₁ r : Residual} {attr : Attr} {ty : CedarType}
  {req : Request} {es : Entities}
  (h : (x₁.evaluate req es).toOption = (r.evaluate req es).toOption) :
  ((x₁.getAttr attr ty).evaluate req es).toOption =
  ((Residual.getAttr r attr ty).evaluate req es).toOption := by
  rw [Residual.evaluate_getAttr, Residual.evaluate_getAttr]
  exact to_option_eq_do₁ (fun x => Spec.getAttr x attr es) h

/-- Soundness of hasAttr when both sides are residual (non-value) -/
theorem hasAttr_sound_of_sound {x₁ r : Residual} {attr : Attr} {ty : CedarType}
  {req : Request} {es : Entities}
  (h : (x₁.evaluate req es).toOption = (r.evaluate req es).toOption) :
  ((x₁.hasAttr attr ty).evaluate req es).toOption =
  ((Residual.hasAttr r attr ty).evaluate req es).toOption := by
  rw [Residual.evaluate_hasAttr, Residual.evaluate_hasAttr]
  exact to_option_eq_do₁ (fun x => Spec.hasAttr x attr es) h

/-- When x₁.evaluate.toOption = some v, getAttr reduces to getAttr on v -/
theorem getAttr_toOption_ok {x₁ : Residual} {attr : Attr} {ty : CedarType}
  {req : Request} {es : Entities} {v : Value}
  (h : x₁.evaluate req es = .ok v) :
  ((x₁.getAttr attr ty).evaluate req es).toOption =
  (Spec.getAttr v attr es).toOption := by
  rw [Residual.evaluate_getAttr, h]; simp [Except.bind, Except.toOption]

/-- When rv.evaluate = .ok (.record m), getAttr on the record gives findOrErr -/
-- This is complex; we'll use rvTargetCorrect directly in the GetAttr proof instead.

@[simp] theorem ResidualValue.evaluate_prim {p : Prim} {req : Request} {es : Entities} :
  (ResidualValue.prim p).evaluate req es = .ok (.prim p) := by
  unfold ResidualValue.evaluate; rfl

@[simp] theorem ResidualValue.evaluate_set {s : Set Value} {req : Request} {es : Entities} :
  (ResidualValue.set s).evaluate req es = .ok (.set s) := by
  unfold ResidualValue.evaluate; rfl

@[simp] theorem ResidualValue.evaluate_ext {x : Ext} {req : Request} {es : Entities} :
  (ResidualValue.ext x).evaluate req es = .ok (.ext x) := by
  unfold ResidualValue.evaluate; rfl

/-! ## Target Correctness Invariant (Paper Definition 5.1) -/

/-- A ResidualValue is target-correct if it evaluates successfully. -/
def rvTargetCorrect (rv : ResidualValue) (req : Request) (es : Entities) : Prop :=
  ∃ v, rv.evaluate req es = .ok v

/-- A Residual is target-correct if every `.val` within it evaluates successfully. -/
inductive rTargetCorrect : Residual → Request → Entities → Prop
  | val {rv ty req es} (h : rvTargetCorrect rv req es) : rTargetCorrect (.val rv ty) req es
  | var {v ty req es} : rTargetCorrect (.var v ty) req es
  | error {ty req es} : rTargetCorrect (.error ty) req es
  | ite {c t e ty req es} (hc : rTargetCorrect c req es) (ht : rTargetCorrect t req es) (he : rTargetCorrect e req es) : rTargetCorrect (.ite c t e ty) req es
  | and {a b ty req es} (ha : rTargetCorrect a req es) (hb : rTargetCorrect b req es) : rTargetCorrect (.and a b ty) req es
  | or {a b ty req es} (ha : rTargetCorrect a req es) (hb : rTargetCorrect b req es) : rTargetCorrect (.or a b ty) req es
  | unaryApp {op x ty req es} (hx : rTargetCorrect x req es) : rTargetCorrect (.unaryApp op x ty) req es
  | binaryApp {op x y ty req es} (hx : rTargetCorrect x req es) (hy : rTargetCorrect y req es) : rTargetCorrect (.binaryApp op x y ty) req es
  | getAttr {x a ty req es} (hx : rTargetCorrect x req es) : rTargetCorrect (.getAttr x a ty) req es
  | hasAttr {x a ty req es} (hx : rTargetCorrect x req es) : rTargetCorrect (.hasAttr x a ty) req es
  | set {xs ty req es} (hxs : ∀ x ∈ xs, rTargetCorrect x req es) : rTargetCorrect (.set xs ty) req es
  | record {m ty req es} (hm : ∀ k v, (k, v) ∈ m → rTargetCorrect v req es) : rTargetCorrect (.record m ty) req es
  | call {xfn args ty req es} (hargs : ∀ x ∈ args, rTargetCorrect x req es) : rTargetCorrect (.call xfn args ty) req es

@[simp] theorem rTargetCorrect_val {rv : ResidualValue} {ty : CedarType} {req : Request} {es : Entities} :
  rTargetCorrect (.val rv ty) req es ↔ rvTargetCorrect rv req es :=
  ⟨fun | .val h => h, .val⟩

@[simp] theorem rTargetCorrect_error {ty : CedarType} {req : Request} {es : Entities} :
  rTargetCorrect (.error ty) req es := .error

theorem rTargetCorrect_unary {op : UnaryOp} {x : Residual} {ty : CedarType} {req : Request} {es : Entities} :
  rTargetCorrect (.unaryApp op x ty) req es ↔ rTargetCorrect x req es :=
  ⟨fun | .unaryApp h => h, .unaryApp⟩

theorem rTargetCorrect_binary {op : BinaryOp} {x y : Residual} {ty : CedarType} {req : Request} {es : Entities} :
  rTargetCorrect (.binaryApp op x y ty) req es ↔ rTargetCorrect x req es ∧ rTargetCorrect y req es :=
  ⟨fun | .binaryApp hx hy => ⟨hx, hy⟩, fun ⟨hx, hy⟩ => .binaryApp hx hy⟩

@[simp] theorem rvTargetCorrect_prim {p : Prim} {req : Request} {es : Entities} :
  rvTargetCorrect (.prim p) req es := ⟨_, ResidualValue.evaluate_prim⟩

@[simp] theorem rvTargetCorrect_set {s : Set Value} {req : Request} {es : Entities} :
  rvTargetCorrect (.set s) req es := ⟨_, ResidualValue.evaluate_set⟩

@[simp] theorem rvTargetCorrect_ext {x : Ext} {req : Request} {es : Entities} :
  rvTargetCorrect (.ext x) req es := ⟨_, ResidualValue.evaluate_ext⟩

/-- Concrete values are always target-correct -/
@[simp] theorem asResidualValue_targetCorrect {v : Value} {req : Request} {es : Entities} :
  rvTargetCorrect v.asResidualValue req es := ⟨v, evaluate_asResidualValue v req es⟩

/-! ## Refinement lemmas (Paper Lemmas 4.1-4.3) -/

/-- Paper Lemma 4.1: absent partial attr → absent concrete attr -/
theorem AttributesRefines.absent_implies_concrete_absent
  {env : TypeEnv} {concrete : List (Attr × Value)}
  {partial_ : List (Attr × PartialAttribute PartialValue)}
  (href : AttributesRefines env concrete partial_)
  {a : Attr}
  (habsent : ∀ pa, (a, pa) ∉ partial_) :
  ∀ v, (a, v) ∉ concrete := by
  cases href with
  | nil => intro v h; cases h
  | cons_present a' v v' t t' hvr har =>
    intro w h; cases h with
    | head => exact habsent _ (.head _)
    | tail _ h => exact absent_implies_concrete_absent har (fun pa hp => habsent pa (.tail _ hp)) w h
  | cons_unknown a' v ty t t' hit har =>
    intro w h; cases h with
    | head => exact habsent _ (.head _)
    | tail _ h => exact absent_implies_concrete_absent har (fun pa hp => habsent pa (.tail _ hp)) w h
  | cons_unknown_neq a' a'' v ty t t' hneq har =>
    intro w h
    exact absent_implies_concrete_absent har (fun pa hp => habsent pa (.tail _ hp)) w h
termination_by concrete.length + partial_.length

/-- Paper Lemma 4.2: present partial attr → concrete value refines -/
theorem AttributesRefines.present_implies_concrete_refines
  {env : TypeEnv} {concrete : List (Attr × Value)}
  {partial_ : List (Attr × PartialAttribute PartialValue)}
  (href : AttributesRefines env concrete partial_)
  {a : Attr} {pv : PartialValue}
  (hpresent : (a, PartialAttribute.present pv) ∈ partial_) :
  ∃ v, (a, v) ∈ concrete ∧ ValueRefines env v pv := by
  cases href with
  | nil => cases hpresent
  | cons_present a' v v' t t' hvr har =>
    cases hpresent with
    | head => exact ⟨v, .head _, hvr⟩
    | tail _ h => have ⟨w, hw, hwr⟩ := present_implies_concrete_refines har h; exact ⟨w, .tail _ hw, hwr⟩
  | cons_unknown a' v ty t t' hit har =>
    cases hpresent with
    | tail _ h => have ⟨w, hw, hwr⟩ := present_implies_concrete_refines har h; exact ⟨w, .tail _ hw, hwr⟩
  | cons_unknown_neq a' a'' v ty t t' hneq har =>
    cases hpresent with
    | tail _ h => have ⟨w, hw, hwr⟩ := present_implies_concrete_refines har h; exact ⟨w, hw, hwr⟩
termination_by concrete.length + partial_.length

/-- If entities refine and a partial entity has a present attribute,
    then the concrete entity has that attribute with a refining value -/
-- Helper to extract AttributesRefines from ValueRefines on records
-- Works around dependent elimination issues with Map wrapper
private def ValueRefines.getAttrsRefines :
  ValueRefines env (.record m₁) (.record m₂) →
  AttributesRefines env m₁.toList m₂.toList
  | .record _ _ _ h => h

-- Direct lemma: if AttributesRefines and partial find? = present pv,
-- then concrete find? returns some value with ValueRefines
theorem AttributesRefines.find_present_refines
  {env : TypeEnv} {concrete : List (Attr × Value)}
  {partial_ : List (Attr × PartialAttribute PartialValue)}
  {attr : Attr} {pv : PartialValue}
  (har : AttributesRefines env concrete partial_)
  (hfind : partial_.find? (fun x => x.fst == attr) = some (attr, .present pv)) :
  ∃ v_attr, concrete.find? (fun x => x.fst == attr) = some (attr, v_attr) ∧
            ValueRefines env v_attr pv := by
  cases har with
  | nil => simp at hfind
  | cons_present a v v' t t' hvr har =>
    simp only [List.find?_cons] at hfind ⊢
    by_cases h : a == attr
    · simp only [h, ↓reduceIte] at hfind ⊢
      have ha : a = attr := beq_iff_eq.mp h
      subst ha
      cases hfind
      exact ⟨v, rfl, hvr⟩
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at hfind ⊢
      exact find_present_refines har hfind
  | cons_unknown a v ty t t' _ har =>
    simp only [List.find?_cons] at hfind ⊢
    by_cases h : a == attr
    · simp [h] at hfind
    · simp [h] at hfind ⊢; exact find_present_refines har hfind
  | cons_unknown_neq a a' v ty t t' hneq har =>
    simp only [List.find?_cons] at hfind ⊢
    by_cases h : a' == attr
    · simp [h] at hfind
    · simp [h] at hfind; exact find_present_refines har hfind
termination_by concrete.length + partial_.length

theorem entity_attr_present_refines
  {env : TypeEnv} {es : Entities} {pes : PartialEntities}
  {uid : EntityUID} {attr : Attr} {pv : PartialValue}
  {attrs : Map Attr (PartialAttribute PartialValue)}
  (href : EntitiesRefine env es pes)
  (hattrs : pes.attrs uid = some attrs)
  (hfind : attrs.find? attr = some (.present pv)) :
  ∃ v_attr, Spec.getAttr (.prim (.entityUID uid)) attr es = .ok v_attr ∧
            ValueRefines env v_attr pv := by
  -- Extract entity from pes
  simp only [PartialEntities.attrs, PartialEntities.get] at hattrs
  cases hpes : pes.find? uid with
  | none => simp [hpes] at hattrs
  | some e₂ =>
    simp [hpes] at hattrs
    -- e₂.attrs = some attrs
    obtain ⟨e₁, hes, hattrs_ref, _⟩ := href uid e₂ hpes
    -- hattrs_ref : PartialIsValid (fun a => ValueRefines env (.record e₁.attrs) (.record a)) e₂.attrs
    -- hattrs : e₂.attrs = some attrs
    -- Extract ValueRefines from PartialIsValid
    have hvr : ValueRefines env (.record e₁.attrs) (.record attrs) := by
      rw [hattrs] at hattrs_ref
      exact match hattrs_ref with | .some _ _ h => h
    have har := hvr.getAttrsRefines
    -- Convert Map.find? to List.find? for use with find_present_refines
    have hfind_list : attrs.toList.find? (fun x => x.fst == attr) = some (attr, .present pv) := by
      simp only [Map.find?] at hfind
      cases hfl : attrs.toList.find? (fun x => x.fst == attr) with
      | none => simp [hfl] at hfind
      | some kv =>
        simp only [hfl, Option.some.injEq] at hfind
        have hk : kv.fst = attr := by
          have := @List.find?_some _ (fun x => x.fst == attr) kv attrs.toList hfl
          simp at this; exact this
        rw [show kv = (kv.fst, kv.snd) from (Prod.eta kv), hk, hfind]
    obtain ⟨v_attr, hfind_c, hvref⟩ := AttributesRefines.find_present_refines har hfind_list
    refine ⟨v_attr, ?_, hvref⟩
    show Spec.getAttr (.prim (.entityUID uid)) attr es = .ok v_attr
    unfold Spec.getAttr Spec.attrsOf Entities.attrs Data.Map.findOrErr
    simp only [Map.find?, Map.toList] at hes hfind_c ⊢
    simp [hes, hfind_c]

/-- Paper Lemma 4.3: unknown partial attr → concrete value exists and is well-typed.
    NOTE: This only holds when the unknown entry was added via cons_unknown (not cons_unknown_neq).
    For entity attributes accessed via EntitiesRefine, cons_unknown_neq represents
    optional schema attributes that may not exist in the concrete record. -/
theorem AttributesRefines.unknown_implies_concrete_typed
  {env : TypeEnv} {concrete : List (Attr × Value)}
  {partial_ : List (Attr × PartialAttribute PartialValue)}
  (href : AttributesRefines env concrete partial_)
  {a : Attr} {ty : CedarType}
  (hunknown : (a, PartialAttribute.unknown ty) ∈ partial_) :
  (∃ v, (a, v) ∈ concrete ∧ InstanceOfType env v ty) ∨
  (∀ v, (a, v) ∉ concrete) := by
  sorry

/-- Paper Lemma 5.1 (Target Correctness): toResidualValue produces values that evaluate correctly.
    If target.evaluate = .ok v_container and ValueRefines env v pv,
    then (toResidualValue target pv ty).evaluate = .ok v. -/
-- Helper: getAttr on a record evaluates to findOrErr
@[simp] theorem getAttr_record_evaluate {m : Map Attr Value} {a : Attr} {ty : CedarType}
  {target : Residual} {req : Request} {es : Entities}
  (htarget : target.evaluate req es = .ok (.record m)) :
  (Residual.getAttr target a ty).evaluate req es = (m.findOrErr a .attrDoesNotExist) := by
  unfold Residual.evaluate
  simp [htarget, Spec.getAttr, Spec.attrsOf]

/-- Record case of Lemma 5.1, proved by induction on AttributesRefines. -/
-- Key-dependent roundtrip: if transforming each kv and then evaluating gives back the original,
-- then the whole mapM gives back the original list
private theorem list_mapM_transform_roundtrip
  {transform : (Attr × β) → γ}
  {evaluate : (Attr × γ) → Except ε Value}
  {partial_ : List (Attr × β)}
  {concrete : List (Attr × Value)}
  (hforall : List.Forall₂ (fun kv_p kv_c =>
    kv_p.fst = kv_c.fst ∧
    evaluate (kv_p.fst, transform kv_p) = .ok kv_c.snd) partial_ concrete) :
  (partial_.map (fun kv => (kv.fst, transform kv))).mapM
    (fun kv => evaluate kv >>= fun v' => pure (kv.fst, v')) = .ok concrete := by
  rw [List.mapM_ok_iff_forall₂]
  induction hforall with
  | nil => exact .nil
  | cons h _ ih =>
    apply List.Forall₂.cons
    · obtain ⟨hk, heval⟩ := h
      simp only [heval, Except.bind_ok, pure, Except.pure]
      congr 1; exact Prod.ext hk rfl
    · exact ih

mutual
/-- Lemma 5.1: toResidualValue evaluates to the concrete value. -/
theorem toResidualValue_evaluate
  {env : TypeEnv} {target : Residual} {v : Value} {pv : PartialValue} {ty : CedarType}
  {req : Request} {es : Entities}
  (htarget : target.evaluate req es = .ok v)
  (href : ValueRefines env v pv) :
  (PartialValue.toResidualValue target pv ty).evaluate req es = .ok v := by
  cases href with
  | prim => simp [PartialValue.toResidualValue, ResidualValue.evaluate]
  | ext => simp [PartialValue.toResidualValue, ResidualValue.evaluate]
  | set => simp [PartialValue.toResidualValue, ResidualValue.evaluate]
  | record a a' har =>
    cases ty with
    | record rty =>
      exact toResidualValue_evaluate_record htarget (fun attr v_a hmem => by
        simp only [Spec.getAttr, Spec.attrsOf, Data.Map.findOrErr, Map.find?, Map.toList]
        sorry -- need (attr, v_a) ∈ a → (.mk a).findOrErr attr = .ok v_a
      ) har
    | _ => sorry
termination_by sizeOf pv

private theorem toResidualValue_evaluate_record
  {env : TypeEnv} {target : Residual} {v_rec : Value}
  {concrete : List (Attr × Value)} {partial_ : List (Attr × PartialAttribute PartialValue)}
  {rty : Map Attr (Qualified CedarType)}
  {req : Request} {es : Entities}
  (htarget : target.evaluate req es = .ok v_rec)
  (hgetattr : ∀ a v_a, (a, v_a) ∈ concrete → Spec.getAttr v_rec a es = .ok v_a)
  (har : AttributesRefines env concrete partial_) :
  (PartialValue.toResidualValue target (.record (.mk partial_)) (.record rty)).evaluate req es =
    .ok (.record (.mk concrete)) := by
  -- Use toResidualValue_forall₂ to build the Forall₂, then connect to the goal
  -- But we can't call toResidualValue_forall₂ here (same termination measure)
  -- Instead, sorry this and prove it outside the mutual block
  sorry
termination_by sizeOf partial_

-- Build the Forall₂ relating partial_ to concrete via the roundtrip property
private theorem toResidualValue_forall₂
  {env : TypeEnv} {target : Residual} {v_rec : Value}
  {concrete : List (Attr × Value)} {partial_ : List (Attr × PartialAttribute PartialValue)}
  {rty : Map Attr (Qualified CedarType)}
  {req : Request} {es : Entities}
  (htarget : target.evaluate req es = .ok v_rec)
  (hgetattr : ∀ a v_a, (a, v_a) ∈ concrete → Spec.getAttr v_rec a es = .ok v_a)
  (har : AttributesRefines env concrete partial_) :
  List.Forall₂ (fun kv_p kv_c =>
    kv_p.fst = kv_c.fst ∧
    ResidualValue.evaluateAttr (kv_p.fst,
      match kv_p.snd with
      | .present pv' =>
        ResidualAttribute.present (PartialValue.toResidualValue (.getAttr target kv_p.fst (.record rty)) pv'
          ((Qualified.getType <$> rty.find? kv_p.fst).getD (.bool .anyBool)))
      | .unknown ty' => ResidualAttribute.unknown target ty') req es = .ok kv_c.snd)
    partial_ concrete := by
  cases har with
  | nil => exact .nil
  | cons_present a v pv t t' hvr har_tl =>
    apply List.Forall₂.cons
    · refine ⟨rfl, ?_⟩
      simp only [ResidualValue.evaluateAttr]
      exact toResidualValue_evaluate
        (by simp [Residual.evaluate, htarget, Except.bind_ok]; exact hgetattr a v (.head _)) hvr
    · exact toResidualValue_forall₂ htarget (fun a' v_a' hmem => hgetattr a' v_a' (.tail _ hmem)) har_tl
  | cons_unknown a v ty' t t' _ har_tl =>
    apply List.Forall₂.cons
    · refine ⟨rfl, ?_⟩
      simp only [ResidualValue.evaluateAttr, Residual.evaluate, htarget, Except.bind_ok]
      exact hgetattr a v (.head _)
    · exact toResidualValue_forall₂ htarget (fun a' v_a' hmem => hgetattr a' v_a' (.tail _ hmem)) har_tl
  | cons_unknown_neq a a' v ty' t t' hneq har_tl =>
    sorry -- cons_unknown_neq: partial has extra entry
termination_by sizeOf partial_
end

/-- Entity-specific version of Lemma 5.1. -/
theorem toResidualValue_entity_evaluate
  {env : TypeEnv} {target : Residual} {uid : EntityUID}
  {v_attr : Value} {pv : PartialValue} {ty : CedarType}
  {attr : Attr} {req : Request} {es : Entities}
  (htarget : target.evaluate req es = .ok (.prim (.entityUID uid)))
  (hgetattr : Spec.getAttr (.prim (.entityUID uid)) attr es = .ok v_attr)
  (href : ValueRefines env v_attr pv) :
  (PartialValue.toResidualValue target pv ty).evaluate req es = .ok v_attr := by
  cases href with
  | prim p => simp [PartialValue.toResidualValue, ResidualValue.evaluate]
  | ext e => simp [PartialValue.toResidualValue, ResidualValue.evaluate]
  | set s => simp [PartialValue.toResidualValue, ResidualValue.evaluate]
  | record a a' har =>
    cases ty with
    | record rty => sorry -- entity record case
    | _ => sorry

/-- Corollary: toResidualValue produces target-correct values -/
theorem toResidualValue_targetCorrect
  {env : TypeEnv} {target : Residual} {v : Value} {pv : PartialValue} {ty : CedarType}
  {req : Request} {es : Entities}
  (htarget : target.evaluate req es = .ok v)
  (href : ValueRefines env v pv) :
  rvTargetCorrect (PartialValue.toResidualValue target pv ty) req es :=
  ⟨v, toResidualValue_evaluate htarget href⟩

-- Key lemma: TPE.evaluate preserves target correctness.
-- This should be proved in a file that imports both ResidualEval and WellTyped.

/-- TargetCorrect → evaluate succeeds -/
theorem rvTargetCorrect_isOk {rv : ResidualValue} {req : Request} {es : Entities} :
  rvTargetCorrect rv req es → (rv.evaluate req es).isOk := by
  intro ⟨v, hv⟩; simp [Except.isOk, Except.toBool, hv]

/-- Phase 1a: toResidual produces target-correct residuals.
    toResidual only creates .lit (concrete prims) and .var — no unknown entries. -/
theorem toResidual_targetCorrect (te : TypedExpr) (req : Request) (es : Entities) :
  rTargetCorrect te.toResidual req es := by
  match te with
  | .lit p ty => simp [TypedExpr.toResidual, rvTargetCorrect_prim]
  | .var v ty => simp [TypedExpr.toResidual]; exact rTargetCorrect.var
  | .ite c t e ty =>
    simp only [TypedExpr.toResidual]
    exact .ite (toResidual_targetCorrect c req es) (toResidual_targetCorrect t req es) (toResidual_targetCorrect e req es)
  | .and a b ty =>
    simp only [TypedExpr.toResidual]
    exact .and (toResidual_targetCorrect a req es) (toResidual_targetCorrect b req es)
  | .or a b ty =>
    simp only [TypedExpr.toResidual]
    exact .or (toResidual_targetCorrect a req es) (toResidual_targetCorrect b req es)
  | .unaryApp op e ty =>
    simp only [TypedExpr.toResidual]
    exact .unaryApp (toResidual_targetCorrect e req es)
  | .binaryApp op a b ty =>
    simp only [TypedExpr.toResidual]
    exact .binaryApp (toResidual_targetCorrect a req es) (toResidual_targetCorrect b req es)
  | .getAttr e attr ty =>
    simp only [TypedExpr.toResidual]
    exact .getAttr (toResidual_targetCorrect e req es)
  | .hasAttr e attr ty =>
    simp only [TypedExpr.toResidual]
    exact .hasAttr (toResidual_targetCorrect e req es)
  | .set ls ty =>
    simp only [TypedExpr.toResidual]
    apply rTargetCorrect.set; intro x hx
    simp [List.map₁_eq_map] at hx
    obtain ⟨te, hte, rfl⟩ := hx
    exact toResidual_targetCorrect te req es
  | .record ls ty => sorry -- needs List.map₂ lemma
  | .call xfn args ty => sorry -- needs List.map₁ lemma
termination_by te

end Cedar.Thm
