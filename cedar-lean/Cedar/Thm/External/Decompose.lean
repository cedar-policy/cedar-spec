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
import Cedar.Validation.Decompose
import Cedar.Thm.External.DecomposeEval
import Cedar.Thm.Validation.RequestEntityValidation
import Cedar.Thm.Validation.EnvironmentValidation

/-!
Authorization is insensitive to action entities outside the request action's
closure (`Schema.actionClosure`).

`isAuthorized_insensitive_to_offclosure_actions` shows that two entity stores
that agree on the request action's closure and on all non-action entities give
the same authorization response, provided no policy has an action-typed entity
literal in a `when`/`unless` body (`Schema.noActionLiteralsInConditions`) and
the schema uses no action type where an entity type is expected
(`Schema.noActionTypedAttrs`). Action literals in the scope (`action == A`,
`action in A`, `action in [A, B]`) are allowed: they compile to
`inₑ action A`, which reads only the request action's own ancestors, and those
are in its closure.

The schema-independent core is in `Cedar.Thm.External.DecomposeEval`.
-/

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

----- Helpers for `isAuthorized_insensitive_to_offclosure_actions` -----

theorem Value.Safe.mono {p q : EntityUID → Prop} {v : Value}
    (hpq : ∀ u, p u → q u) (h : Value.Safe p v) : Value.Safe q v := by
  induction h with
  | bool b => exact .bool b
  | int i => exact .int i
  | string str => exact .string str
  | uid u hu => exact .uid u (hpq u hu)
  | set s _ ih => exact .set s ih
  | record m _ ih => exact .record m ih
  | ext x => exact .ext x

theorem entityTypesAll_record_mem {ok : EntityType → Bool} {rty : RecordType}
    {k : Attr} {qty : QualifiedType}
    (h : (CedarType.record rty).entityTypesAll ok = true) (hmem : (k, qty) ∈ rty.toList) :
    qty.getType.entityTypesAll ok = true := by
  simp only [CedarType.entityTypesAll, List.all_eq_true] at h
  have := h ⟨(k, qty), hmem⟩ (List.mem_attach _ _)
  cases qty <;> simpa [Qualified.getType] using this

/-- A value that conforms to a type mentioning only declared entity types holds
    no action UIDs. -/
theorem instanceOfType_noAction {env : TypeEnv} {v : Value} {ty : CedarType}
    (hdisj : ∀ uid, env.acts.contains uid → ¬ env.ets.contains uid.ty)
    (h : Cedar.Thm.InstanceOfType env v ty) :
    ty.entityTypesAll env.ets.contains = true →
    Value.Safe (fun u => env.acts.contains u = false) v := by
  induction h with
  | instance_of_bool b _ _ => intro _; exact .bool b
  | instance_of_int => intro _; exact .int _
  | instance_of_string => intro _; exact .string _
  | instance_of_entity e ety h₁ =>
    intro hty
    simp only [CedarType.entityTypesAll] at hty
    obtain ⟨hety, _⟩ := h₁
    subst hety
    apply Value.Safe.uid
    cases hc : env.acts.contains e
    · rfl
    · exact absurd hty (hdisj e hc)
  | instance_of_set s ty _ ih =>
    intro hty
    simp only [CedarType.entityTypesAll] at hty
    exact .set s fun v hv => ih v hv hty
  | instance_of_record r rty h₁ _ _ ih =>
    intro hty
    apply Value.Safe.record
    intro k v hk
    have hc : rty.contains k := h₁ k (Map.find?_some_implies_contains hk)
    obtain ⟨qty, hq⟩ := Map.contains_iff_some_find?.mp hc
    exact ih k v qty hk hq (entityTypesAll_record_mem hty (Map.find?_mem_toList hq))
  | instance_of_ext x _ _ => intro _; exact .ext x

theorem actionType?_of_contains {acts : ActionSchema} {u : EntityUID}
    (h : acts.contains u = true) : acts.actionType? u.ty = true := by
  simp only [ActionSchema.contains, Option.isSome_iff_exists] at h
  obtain ⟨entry, hentry⟩ := h
  have hmem := Map.find?_mem_toList hentry
  simp only [ActionSchema.actionType?, Map.keys, Set.any, List.any_eq_true, beq_iff_eq]
  exact ⟨u, List.mem_map.mpr ⟨(u, entry), hmem, rfl⟩, rfl⟩

theorem actionClosure_self_or_absent (s : Schema) (uid : EntityUID) :
    s.acts.contains uid = false ∨ (s.actionClosure uid).contains uid = true := by
  unfold Schema.actionClosure
  cases h : s.acts.find? uid with
  | none => left; simp [ActionSchema.contains, h]
  | some entry =>
    right
    rw [Set.contains_prop_bool_equiv, Set.mem_make]
    exact List.mem_cons_self ..

/--
Authorization is insensitive to action entities outside the request action's
closure, when no policy has an action literal in a `when`/`unless` body and the
schema uses no action type where an entity type is expected.

Two entity stores that agree on `uid`'s action closure and on all non-action
entities yield the same `isAuthorized` response, even if they disagree on action
entities outside the closure.

Why each premise is needed:

* `hnolits`: a condition such as `Action::"x" in Action::"y"` reads the entity
  data of `x`, which may be outside the closure.
* `hnoacttys`: without it an action UID can reach evaluation as a value, for
  example through an action-typed context field or an action-typed principal.
  See the counterexamples on `Schema.noActionTypedAttrs`.
* `hwf`, `hr`, `he`: `noActionTypedAttrs` constrains only the schema. Request
  and entity validation are what make the actual principal, resource, context,
  attribute, tag, and ancestor values conform to it. Only the full store `es₁`
  is required to validate; the other store `es₂` is constrained through
  `hclosure` and `hnonaction`.
-/
theorem isAuthorized_insensitive_to_offclosure_actions
    (s : Schema) (uid : EntityUID) (req : Request) (policies : Policies)
    (es₁ es₂ : Entities)
    (hwf : s.validateWellFormed = .ok ())
    (hr : validateRequest s req = .ok ())
    (he : validateEntities s es₁ = .ok ())
    (hreq : req.action = uid)
    (hnolits : s.noActionLiteralsInConditions policies = true)
    (hnoacttys : s.noActionTypedAttrs = true)
    (hclosure : ∀ a, (s.actionClosure uid).contains a = true → es₁.find? a = es₂.find? a)
    (hnonaction : ∀ k, s.acts.contains k = false → es₁.find? k = es₂.find? k) :
  isAuthorized req es₁ policies = isAuthorized req es₂ policies
:= by
  let safe : EntityUID → Prop := fun u =>
    s.acts.contains u = false ∨ (s.actionClosure uid).contains u = true
  have hinst := Cedar.Thm.request_and_entities_validate_implies_instance_of_wf_schema s req es₁ hwf hr he
  obtain ⟨env, henv, hwfenv, hreqty, hschema⟩ := hinst
  obtain ⟨hets, hacts, entry, hentry, hprin, hres, hctx⟩ := Cedar.Thm.mem_environments henv
  have hdisj : ∀ u, env.acts.contains u → ¬ env.ets.contains u.ty := hwfenv.2.1.2.2.1
  simp only [Schema.noActionTypedAttrs, Schema.recordMentionsNoActionTypes, Bool.and_eq_true,
    List.all_eq_true] at hnoacttys
  obtain ⟨hnoEts, hnoActs⟩ := hnoacttys
  -- Anything typed by a declared entity type is safe.
  have hnoaction : ∀ {v ty}, Cedar.Thm.InstanceOfType env v ty →
      ty.entityTypesAll s.ets.contains = true → Value.Safe safe v := by
    intro v ty hv hty
    rw [← hets] at hty
    exact Value.Safe.mono (fun u hu => .inl (hacts ▸ hu)) (instanceOfType_noAction hdisj hv hty)
  have hentity_safe : ∀ {u : EntityUID}, s.ets.contains u.ty = true → safe u := by
    intro u hu
    left
    cases hc : s.acts.contains u
    · rfl
    · exact absurd (hets ▸ hu) (hdisj u (hacts ▸ hc))
  -- The stores agree on safe UIDs.
  have hagree : ∀ u, safe u → es₁.find? u = es₂.find? u := by
    intro u hu
    cases hu with
    | inl h => exact hnonaction u h
    | inr h => exact hclosure u h
  -- Attribute and tag values in `es₁` are safe.
  have hstore : StoreSafe safe es₁ := by
    intro u d hd
    cases hschema.1 u d hd with
    | inl hent =>
      obtain ⟨eentry, heentry, _, hattrs, _, htags⟩ := hent
      have hval : eentry ∈ s.ets.values :=
        Map.in_list_in_values (Map.find?_mem_toList (hets ▸ heentry))
      have ⟨hattrsOk, htagsOk⟩ := hnoEts eentry hval
      constructor
      · have := hnoaction hattrs hattrsOk
        cases this with
        | record _ h => exact h
      · intro k v hk
        unfold Cedar.Thm.InstanceOfEntityTags at htags
        cases ht : eentry.tags? with
        | none =>
          simp only [ht] at htags
          simp [htags] at hk
        | some tty =>
          simp only [ht] at htags htagsOk
          simp only [Option.map_some, Option.getD_some] at htagsOk
          exact hnoaction (htags v (Map.in_list_in_values (Map.find?_mem_toList hk))) htagsOk
    | inr hact =>
      obtain ⟨hattrs, htags, _⟩ := hact
      constructor
      · intro k v hk; simp [hattrs] at hk
      · intro k v hk; simp [htags] at hk
  -- The request is safe.
  have hreqsafe : RequestSafe safe req := by
    obtain ⟨hp, ha, hrs, hc⟩ := hreqty
    have haval : entry ∈ s.acts.values := Map.in_list_in_values hentry
    have ⟨⟨hctxOk, hprinOk⟩, hresOk⟩ := hnoActs entry haval
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨hpty, _⟩ := hp
      apply hentity_safe
      rw [← hpty]
      exact hprinOk _ ((Set.mem_elts_iff_mem_set _ _).mpr hprin)
    · rw [hreq]
      exact actionClosure_self_or_absent s uid
    · obtain ⟨hrty, _⟩ := hrs
      apply hentity_safe
      rw [← hrty]
      exact hresOk _ ((Set.mem_elts_iff_mem_set _ _).mpr hres)
    · rw [hctx] at hc
      exact hnoaction hc hctxOk
  -- Condition literals are safe.
  have hlits : ∀ p ∈ policies, ∀ c ∈ p.condition, ∀ u ∈ c.body.literalUIDs, safe u := by
    intro p hp c hc u hu
    simp only [Schema.noActionLiteralsInConditions, List.all_eq_true, Bool.not_eq_true'] at hnolits
    have hmem : u ∈ p.conditionLiteralUIDs :=
      List.mem_mem_implies_mem_mapUnion (f := fun c : Condition => c.body.literalUIDs) hu hc
    have hnot := hnolits p hp u ((Set.mem_elts_iff_mem_set _ _).mpr hmem)
    left
    cases hcu : s.acts.contains u
    · rfl
    · rw [actionType?_of_contains hcu] at hnot; cases hnot
  exact isAuthorized_agree hagree hstore hreqsafe hlits

end Cedar.Validation
