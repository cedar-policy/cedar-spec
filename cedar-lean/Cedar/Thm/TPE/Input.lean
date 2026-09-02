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

import Cedar.TPE.Input
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.Validation

/-!
This file defines theorems related to the inputs of TPE.
-/

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

theorem decide_eq_implies_eq {α} [DecidableEq α] {y : α} :
  ∀ x, decide (x = y) → x = y := by
      simp only [decide_eq_true_eq, imp_self, implies_true]

inductive PartialIsValid {α} (p : α → Prop) (o : Option α) : Prop
  | some (x : α) (heq : o = .some x) (h : p x) :
    PartialIsValid p o
  | none (heq : o = .none) :
    PartialIsValid p o

@[simp]
theorem PartialIsValid.some_inv {p : α → Prop} {x : α} :  (PartialIsValid p (.some x)) ↔ p x := by
  constructor
  · intro h
    cases h with
    | some y heq hy => simp only [Option.some.injEq] at heq; subst heq; exact hy
    | none heq => simp at heq
  · exact some _ rfl

theorem partial_is_valid_rfl {f : α → Bool} {p : α → Prop} {o : Option α} :
  (∀ x, f x = true → p x) → partialIsValid o f → PartialIsValid p o
:= by
  intro h₁ h₂
  cases o with
  | none => exact .none rfl
  | some x =>
    simp only [partialIsValid, Option.map_some, Option.getD_some] at h₂
    exact .some x rfl (h₁ x h₂)

/-- What the partial attribute state `s` claims about a concrete lookup result.-/
inductive AttrStateConsistent : AttrState → Option Value → Prop where
  | value {v : Value} :
    AttrStateConsistent (.value v) (.some v)
  | partialRecord {r : PartialRecord} {m : Data.Map Attr Value}
    (hrwf : r.WellFormed) (hmwf : m.WellFormed)
    (h : ∀ a, AttrStateConsistent (r.attr a) (m.find? a)) :
    AttrStateConsistent (.partialRecord r) (.some (.record m))
  | present {v : Value} :
    AttrStateConsistent .present (.some v)
  | absent :
    AttrStateConsistent .absent .none
  | unknown {o : Option Value} :
    AttrStateConsistent .unknown o

def PartialRecordConsistent (r : PartialRecord) (m : Data.Map Attr Value) : Prop :=
  ∀ a, AttrStateConsistent (r.attr a) (m.find? a)

theorem AttrStateConsistent.value_inv {v : Value} {o : Option Value}
  (h : AttrStateConsistent (.value v) o) : o = .some v
:= by cases h; rfl

theorem AttrStateConsistent.present_inv {o : Option Value}
  (h : AttrStateConsistent .present o) : ∃ v, o = .some v
:= by cases h; exact ⟨_, rfl⟩

theorem AttrStateConsistent.absent_inv {o : Option Value}
  (h : AttrStateConsistent .absent o) : o = .none
:= by cases h; rfl

theorem AttrStateConsistent.partialRecord_inv {r : PartialRecord} {o : Option Value}
  (h : AttrStateConsistent (.partialRecord r) o) :
  ∃ m, o = .some (.record m) ∧ r.WellFormed ∧ m.WellFormed ∧ PartialRecordConsistent r m
:= by cases h with | partialRecord hrwf hmwf h => exact ⟨_, rfl, hrwf, hmwf, h⟩

theorem AttrStateConsistent.exists_inv {s : AttrState} {o : Option Value}
  (hs : s.exists? = true) (h : AttrStateConsistent s o) : ∃ v, o = .some v
:= by
  cases h <;> simp only [AttrState.exists?, Bool.false_eq_true] at hs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

def AttrsRefine (es : Entities) (uid : EntityUID) (r : PartialRecord) : Prop :=
  ∃ e, es.find? uid = .some e ∧ PartialRecordConsistent r e.attrs

def TagsRefine (es : Entities) (uid : EntityUID) (r : PartialRecord) : Prop :=
  ∃ e, es.find? uid = .some e ∧ PartialRecordConsistent r e.tags

def ContextRefines (m : Data.Map Attr Value) (r : PartialRecord) : Prop :=
  r.WellFormed ∧ m.WellFormed ∧ PartialRecordConsistent r m

theorem ContextRefines.toAttrState {m : Data.Map Attr Value} {r : PartialRecord}
  (h : ContextRefines m r) :
  AttrStateConsistent (.partialRecord r) (.some (.record m))
:= .partialRecord h.1 h.2.1 h.2.2

def RequestRefines (req : Request) (preq : PartialRequest) : Prop :=
  PartialIsValid (· = req.principal) preq.principal.asEntityUID ∧
  req.action = preq.action ∧
  PartialIsValid (· = req.resource) preq.resource.asEntityUID  ∧
  PartialIsValid (ContextRefines req.context) preq.context ∧
  preq.principal.ty = req.principal.ty ∧
  preq.resource.ty = req.resource.ty

def EntitiesRefine (es : Entities) (pes : PartialEntities) : Prop :=
   ∀ uid ped, pes.find? uid = some ped →
    PartialIsValid (AttrsRefine es uid) ped.attrs ∧
    PartialIsValid (· = es.ancestorsOrEmpty uid) ped.ancestors  ∧
    PartialIsValid (TagsRefine es uid) ped.tags

theorem sizeOf_attr_lt {r : PartialRecord} {a : Attr} :
  sizeOf (r.attr a) < sizeOf r
:= by
  have hmk : sizeOf r = 1 + sizeOf r.toList := by
    cases r; simp only [Data.Map.toList_mk_id, Data.Map.mk.sizeOf_spec]
  simp only [PartialRecord.attr]
  cases hfind : r.find? a with
  | none =>
    have hpos : 0 < sizeOf r.toList := by
      cases hl : r.toList with
      | nil => simp only [List.nil.sizeOf_spec]; omega
      | cons hd tl => simp only [List.cons.sizeOf_spec]; omega
    simp only [Option.getD_none, hmk, AttrState.unknown.sizeOf_spec]
    omega
  | some s =>
    have hmem := Data.Map.find?_mem_toList hfind
    have hlt : sizeOf ((a, s) : Attr × AttrState).snd < 1 + sizeOf r.toList :=
      List.sizeOf_snd_lt_sizeOf_list hmem
    simp only at hlt
    simp only [Option.getD_some, hmk]
    omega

theorem consistentWith_attr {r : PartialRecord} {m : Data.Map Attr Value}
  (h : PartialRecord.consistentWith r m = true) (a : Attr) :
  (r.attr a).consistentWith (m.find? a) = true
:= by
  simp only [PartialRecord.consistentWith, List.all_eq_true, List.attach₂] at h
  simp only [PartialRecord.attr]
  cases hfind : r.find? a with
  | none => simp only [Option.getD_none, AttrState.consistentWith]
  | some s =>
    have hmem := Data.Map.find?_mem_toList hfind
    simp only [Data.Map.toList] at hmem
    have hp : sizeOf ((a, s) : Attr × AttrState).snd < 1 + sizeOf r.toList :=
      List.sizeOf_snd_lt_sizeOf_list hmem
    have := h ⟨(a, s), hp⟩ ((List.mem_pmap_subtype _ _ (a, s) hp).mpr hmem)
    simpa only [Option.getD_some] using this

theorem attr_state_consistent_of_consistentWith {s : AttrState} {o : Option Value} :
  s.consistentWith o = true → AttrStateConsistent s o
:= by
  intro h
  cases s with
  | value v =>
    cases o with
    | none => simp only [AttrState.consistentWith, Bool.false_eq_true] at h
    | some v' =>
      simp only [AttrState.consistentWith, beq_iff_eq] at h
      subst h
      exact .value
  | partialRecord r =>
    cases o with
    | none => simp only [AttrState.consistentWith, Bool.false_eq_true] at h
    | some v' =>
      cases v' with
      | record m =>
        rw [AttrState.consistentWith] at h
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hrwf, hmwf⟩, h⟩ := h
        refine .partialRecord (Data.Map.wellFormed_correct.mp hrwf)
          (Data.Map.wellFormed_correct.mp hmwf) (fun a => ?_)
        have hsz : sizeOf (PartialRecord.attr r a) < sizeOf (AttrState.partialRecord r) := by
          have h₁ := @sizeOf_attr_lt r a
          simp only [AttrState.partialRecord.sizeOf_spec]
          omega
        exact attr_state_consistent_of_consistentWith (consistentWith_attr h a)
      | prim _ | set _ | ext _ =>
        simp only [AttrState.consistentWith, Bool.false_eq_true] at h
  | present =>
    cases o with
    | none => simp only [AttrState.consistentWith, Bool.false_eq_true] at h
    | some v => exact .present
  | absent =>
    cases o with
    | none => exact .absent
    | some v => simp only [AttrState.consistentWith, Bool.false_eq_true] at h
  | unknown => exact .unknown
termination_by sizeOf s

theorem partial_record_consistent_of_consistentWith {r : PartialRecord} {m : Data.Map Attr Value} :
  PartialRecord.consistentWith r m = true → PartialRecordConsistent r m
:= fun h a => attr_state_consistent_of_consistentWith (consistentWith_attr h a)


/-- Concrete request `req` and entities `es` refine their partial counterparts
`peq` and `pes`.
-/
def RequestAndEntitiesRefine (req : Request) (es : Entities) (preq : PartialRequest) (pes : PartialEntities) : Prop :=
  RequestRefines req preq ∧ EntitiesRefine es pes

theorem validatePartialRequest_ok_environment? {schema : Schema} {req : PartialRequest} {env : TypeEnv} :
  validatePartialRequest schema req = .ok env →
  schema.environment? req.principal.ty req.resource.ty req.action = .some env
:= by
  intro h
  simp only [validatePartialRequest] at h
  split at h
  · rename_i env' heq
    split at h <;> try contradiction
    simp only [Except.ok.injEq] at h
    simp [h, heq]
  · contradiction

theorem entitiesIsConsistent_implies_refines {es : Entities} {pes : PartialEntities} :
  entitiesIsConsistent es pes → EntitiesRefine es pes
:= by
  intro h uid data₂ hᵢ
  replace hᵢ := Data.Map.find?_mem_toList hᵢ
  simp only [entitiesIsConsistent, List.all_eq_true, Prod.forall] at h
  specialize h uid data₂ hᵢ
  split at h <;> simp only [Bool.false_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨h₂₁, h₂₂⟩, h₂₃⟩
  rename_i data₁ heq
  have hanc : es.ancestorsOrEmpty uid = data₁.ancestors := by
    simp only [Entities.ancestorsOrEmpty, heq]
  and_intros
  · exact partial_is_valid_rfl (fun r hr => ⟨data₁, heq, partial_record_consistent_of_consistentWith hr⟩) h₂₁
  · exact partial_is_valid_rfl (fun _ hx => hanc ▸ decide_eq_implies_eq _ hx) h₂₂
  · exact partial_is_valid_rfl (fun r hr => ⟨data₁, heq, partial_record_consistent_of_consistentWith hr⟩) h₂₃

theorem requestIsConsistent_implies_refines {req : Request} {preq : PartialRequest} :
  requestIsConsistent req preq →
  RequestRefines req preq
:= by
  intro h₁
  simp only [requestIsConsistent, Bool.and_eq_true, decide_eq_true_eq] at h₁
  obtain ⟨⟨⟨⟨⟨h_pty, h_rty⟩, h₁₁⟩, h₁₂⟩, h₁₃⟩, h₁₄⟩ := h₁
  and_intros
  · exact partial_is_valid_rfl decide_eq_implies_eq h₁₁
  · exact h₁₂
  · exact partial_is_valid_rfl decide_eq_implies_eq h₁₃
  · exact partial_is_valid_rfl (fun _ hx => by
      simp only [Bool.and_eq_true] at hx
      exact ⟨Data.Map.wellFormed_correct.mp hx.1.1, Data.Map.wellFormed_correct.mp hx.1.2,
        partial_record_consistent_of_consistentWith hx.2⟩) h₁₄
  · exact h_pty
  · exact h_rty

/-- Requests and entities that pass `isValidAndConsistent` satisfy `RequestAndEntitiesRefine`.  -/
theorem consistent_checks_ensure_refinement {schema : Schema} {req : Request} {es : Entities} {preq : PartialRequest} {pes : PartialEntities} :
  isValidAndConsistent schema req es preq pes = .ok () → RequestAndEntitiesRefine req es preq pes
:= by
  intro h
  simp only [isValidAndConsistent] at h
  split at h <;> try cases h
  rename_i env heq
  rcases do_eq_ok₂ h with ⟨h₁, h₂⟩
  constructor
  case _ =>
    have h_consistent : requestIsConsistent req preq := by
      simp only [isValidAndConsistent.requestIsValidAndConsistent] at h₁
      split at h₁ <;> simp_all
    exact requestIsConsistent_implies_refines h_consistent
  case _ =>
    have h₃ : isValidAndConsistent.entitiesIsValidAndConsistent es pes env = .ok ()
    := by
      simp only [isValidAndConsistent.envIsWellFormed, bind, Except.bind] at h₂
      split at h₂ <;> simp_all
    have h_consistent : entitiesIsConsistent es pes := by
      simp only [isValidAndConsistent.entitiesIsValidAndConsistent] at h₃
      split at h₃ <;> simp_all
    exact entitiesIsConsistent_implies_refines h_consistent

end Cedar.Thm
