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

import CedarGen.Relational.SchemaGenFFacts
import Cedar.Thm.Validation.Relational.WellFormed

/-! # The types `GenTypeEnvF` draws

`TyF` at `chk` describes exactly the types `EnvAssumptions` allows (`TyWf` and `TypeValid`), and
with `wfMaps` and `wfRest` exactly the ones `validateWellFormed` allows (`CedarTypeWF` and
`CedarTypeLifted`); without `chk`, every type. Entity types are referred to through two lists,
the entity type names `ks` and the action types `ats`. -/

namespace Cedar.Validation.Relational.SchemaGen

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Cedar.Validation.Relational.Schema

/-! ## References -/

theorem RefIf.mem {i ks ats x} (h : RefIf true i ks ats x) : x ∈ ks ∨ x ∈ ats := by
  cases h
  case entTT h => exact .inl (definedEntityType_iff_mem.mp h)
  case entTF h => exact .inl (definedEntityType_iff_mem.mp h)
  case actTF h => exact .inr (definedEntityType_iff_mem.mp h)

theorem refIf_of_mem {ks ats x} (h : x ∈ ks ∨ x ∈ ats) : RefIf true false ks ats x := by
  rcases h with h | h
  · exact .entTF _ _ _ (definedEntityType_iff_mem.mpr h)
  · exact .actTF _ _ _ (definedEntityType_iff_mem.mpr h)

theorem refIf_ent {i ks ats x} (h : x ∈ ks) : RefIf true i ks ats x := by
  cases i
  · exact .entTF _ _ _ (definedEntityType_iff_mem.mpr h)
  · exact .entTT _ _ _ (definedEntityType_iff_mem.mpr h)

theorem RefAny.mem {ks ats x} (h : RefAny ks ats x) : x ∈ ks ∨ x ∈ ats := by
  cases h
  case ent h => exact .inl (definedEntityType_iff_mem.mp h)
  case act h => exact .inr (definedEntityType_iff_mem.mp h)

theorem refAny_of_mem {ks ats x} (h : x ∈ ks ∨ x ∈ ats) : RefAny ks ats x := by
  rcases h with h | h
  · exact .ent _ _ _ (definedEntityType_iff_mem.mpr h)
  · exact .act _ _ _ (definedEntityType_iff_mem.mpr h)

theorem boolIf_false (b : BoolType) : BoolIf false b := by
  cases b
  · exact .anyF
  · exact .ttF
  · exact .ffF

/-! ## Soundness -/

mutual

/-- Checked types are `TyWf` and `TypeValid`. -/
theorem TyF.tyWf_typeValid {m d i ks ats} {env : TypeEnv}
    (hv : ∀ x, x ∈ ks ∨ x ∈ ats → ValidEntityType x env.ets env.acts) :
    {ty : CedarType} → TyF m d i true ks ats ty → TyWf ty ∧ TypeValid env ty
  | _, .bool _ _ => ⟨.bool _, .bool _⟩
  | _, .int => ⟨.int, .int⟩
  | _, .string => ⟨.string, .string⟩
  | _, .decimal => ⟨.ext _, .ext _⟩
  | _, .ipAddr => ⟨.ext _, .ext _⟩
  | _, .datetime => ⟨.ext _, .ext _⟩
  | _, .duration => ⟨.ext _, .ext _⟩
  | _, .entity _ h => ⟨.entity _, .entity _ (hv _ h.mem)⟩
  | _, .set _ h =>
    have h' := TyF.tyWf_typeValid hv h
    ⟨.set _ h'.1, .set _ h'.2⟩
  | _, .record attrs raw hf ha =>
    have hraw := FieldsF.tyWf_typeValid hv hf
    ⟨.record (Map.mk attrs) (ha.nodup) (fun q hq => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        exact (hraw p (ha.sub p hp)).1),
     .record attrs (fun p hp => (hraw p (ha.sub p hp)).2)⟩

theorem FieldsF.tyWf_typeValid {m d i ks ats} {env : TypeEnv}
    (hv : ∀ x, x ∈ ks ∨ x ∈ ats → ValidEntityType x env.ets env.acts) :
    {fs : List (Attr × QualifiedType)} → FieldsF m d i true ks ats fs →
      ∀ p ∈ fs, TyWfQ p.2 ∧ TypeValid env p.2.getType
  | _, .nil => fun _ h => absurd h List.not_mem_nil
  | _, .req _ _ _ h₁ h₂ => fun p hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · have := TyF.tyWf_typeValid hv h₁
      exact ⟨.required _ this.1, this.2⟩
    · exact FieldsF.tyWf_typeValid hv h₂ p hp
  | _, .opt _ _ _ h₁ h₂ => fun p hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · have := TyF.tyWf_typeValid hv h₁
      exact ⟨.optional _ this.1, this.2⟩
    · exact FieldsF.tyWf_typeValid hv h₂ p hp

end

mutual

/-- With `wfMaps` and `wfRest`, checked types are well-formed and lifted. -/
theorem TyF.cedarTypeWF {i ks ats} {ets : EntitySchema} {acts : ActionSchema}
    (hv : ∀ x, x ∈ ks ∨ x ∈ ats → EntityTypeWF ets acts x) :
    {ty : CedarType} → TyF true true i true ks ats ty → CedarTypeWF ets acts ty ∧ CedarTypeLifted ty
  | _, .bool _ h => by cases h; exact ⟨.bool _ _ _, .bool⟩
  | _, .int => ⟨.int _ _, .int⟩
  | _, .string => ⟨.string _ _, .string⟩
  | _, .decimal => ⟨.ext _ _ _, .ext _⟩
  | _, .ipAddr => ⟨.ext _ _ _, .ext _⟩
  | _, .datetime => ⟨.ext _ _ _, .ext _⟩
  | _, .duration => ⟨.ext _ _ _, .ext _⟩
  | _, .entity _ h => ⟨.entity _ _ _ (hv _ h.mem), .entity _⟩
  | _, .set _ h =>
    have h' := TyF.cedarTypeWF hv h
    ⟨.set _ _ _ h'.1, .set _ h'.2⟩
  | _, .record attrs raw hf ha =>
    have hraw := FieldsF.cedarTypeWF hv hf
    ⟨.record _ _ attrs (ha.sorted rfl) (attrsWF_of_forall fun p hp => (hraw p (ha.sub p hp)).1),
     .record _ (attrsLifted_of_forall fun p hp => (hraw p (ha.sub p hp)).2)⟩

theorem FieldsF.cedarTypeWF {i ks ats} {ets : EntitySchema} {acts : ActionSchema}
    (hv : ∀ x, x ∈ ks ∨ x ∈ ats → EntityTypeWF ets acts x) :
    {fs : List (Attr × QualifiedType)} → FieldsF true true i true ks ats fs →
      ∀ p ∈ fs, QualifiedTypeWF ets acts p.2 ∧ QualifiedTypeLifted p.2
  | _, .nil => fun _ h => absurd h List.not_mem_nil
  | _, .req _ _ _ h₁ h₂ => fun p hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · have := TyF.cedarTypeWF hv h₁
      exact ⟨.required _ _ _ this.1, .required _ this.2⟩
    · exact FieldsF.cedarTypeWF hv h₂ p hp
  | _, .opt _ _ _ h₁ h₂ => fun p hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · have := TyF.cedarTypeWF hv h₁
      exact ⟨.optional _ _ _ this.1, .optional _ this.2⟩
    · exact FieldsF.cedarTypeWF hv h₂ p hp

end

/-! ## Completeness -/

theorem fieldsF_of_forall {m d i c ks ats} :
    {l : List (Attr × QualifiedType)} → (∀ p ∈ l, TyF m d i c ks ats p.2.getType) →
      FieldsF m d i c ks ats l
  | [], _ => .nil
  | (k, .required t) :: l, h =>
    .req _ _ _ (h _ List.mem_cons_self) (fieldsF_of_forall fun p hp => h p (List.mem_cons_of_mem _ hp))
  | (k, .optional t) :: l, h =>
    .opt _ _ _ (h _ List.mem_cons_self) (fieldsF_of_forall fun p hp => h p (List.mem_cons_of_mem _ hp))

mutual

/-- Every `TyWf`, `TypeValid` type is a checked type. -/
theorem tyF_of_tyWf {ks ats} {env : TypeEnv}
    (hv : ∀ x, ValidEntityType x env.ets env.acts → x ∈ ks ∨ x ∈ ats) :
    {ty : CedarType} → TyWf ty → TypeValid env ty → TyF false false false true ks ats ty
  | _, .bool b, _ => .bool _ (boolIf_false b)
  | _, .int, _ => .int
  | _, .string, _ => .string
  | _, .entity _, .entity _ h => .entity _ (refIf_of_mem (hv _ h))
  | _, .ext .ipAddr, _ => .ipAddr
  | _, .ext .decimal, _ => .decimal
  | _, .ext .datetime, _ => .datetime
  | _, .ext .duration, _ => .duration
  | _, .set _ h, .set _ hval => .set _ (tyF_of_tyWf hv h hval)
  | _, .record ⟨rts⟩ hnd hq, .record _ hrts =>
    .record rts rts (fieldsF_of_forall fun p hp =>
      tyF_of_tyWfQ hv (hq p.2 (List.mem_map_of_mem hp)) (hrts p hp))
      (by have := AttrArr.dedupTF rts; rwa [dedupKeys_of_nodup (xs := rts) hnd] at this)

theorem tyF_of_tyWfQ {ks ats} {env : TypeEnv}
    (hv : ∀ x, ValidEntityType x env.ets env.acts → x ∈ ks ∨ x ∈ ats) :
    {q : QualifiedType} → TyWfQ q → TypeValid env q.getType → TyF false false false true ks ats q.getType
  | _, .required _ h, hval => tyF_of_tyWf hv h hval
  | _, .optional _ h, hval => tyF_of_tyWf hv h hval

end

mutual

/-- Every well-formed, lifted type is a checked type at `wfMaps` and `wfRest`. -/
theorem tyF_of_cedarTypeWF {ks ats} {ets : EntitySchema} {acts : ActionSchema}
    (hv : ∀ x, EntityTypeWF ets acts x → x ∈ ks ∨ x ∈ ats) :
    {ty : CedarType} → CedarTypeWF ets acts ty → CedarTypeLifted ty → TyF true true false true ks ats ty
  | _, .bool _ _ _, hl => by cases hl; exact .bool _ .anyT
  | _, .int _ _, _ => .int
  | _, .string _ _, _ => .string
  | _, .entity _ _ _ h, _ => .entity _ (refIf_of_mem (hv _ h))
  | _, .set _ _ _ h, hl => by
    cases hl
    exact .set _ (tyF_of_cedarTypeWF hv h ‹_›)
  | _, .record _ _ rty hs ha, hl => by
    cases hl
    refine .record rty rty (fieldsF_of_attrsWF hv ha ‹_›) ?_
    have := AttrArr.sortTT rty
    rwa [canonicalize_fst_of_keysSorted hs] at this
  | _, .ext _ _ x, _ => by
    cases x
    · exact .ipAddr
    · exact .decimal
    · exact .datetime
    · exact .duration

theorem fieldsF_of_attrsWF {ks ats} {ets : EntitySchema} {acts : ActionSchema}
    (hv : ∀ x, EntityTypeWF ets acts x → x ∈ ks ∨ x ∈ ats) :
    {l : List (Attr × QualifiedType)} → AttrsWF ets acts l → AttrsLifted l →
      FieldsF true true false true ks ats l
  | _, .nil _ _, _ => .nil
  | _, .cons _ _ _ _ _ hq hr, hl => by
    cases hl
    next hql hrl =>
    cases hq
    case optional h =>
      cases hql
      exact .opt _ _ _ (tyF_of_cedarTypeWF hv h ‹_›) (fieldsF_of_attrsWF hv hr hrl)
    case required h =>
      cases hql
      exact .req _ _ _ (tyF_of_cedarTypeWF hv h ‹_›) (fieldsF_of_attrsWF hv hr hrl)

end

mutual

/-- Unchecked types are any type. -/
theorem tyF_any {ks ats} : (ty : CedarType) → TyF false false false false ks ats ty
  | .bool b => .bool _ (boolIf_false b)
  | .int => .int
  | .string => .string
  | .entity _ => .entity _ (.anyFF _ _ _)
  | .set t => .set _ (tyF_any t)
  | .record ⟨l⟩ => .record l l (fieldsF_any l) (.rawFF l)
  | .ext .ipAddr => .ipAddr
  | .ext .decimal => .decimal
  | .ext .datetime => .datetime
  | .ext .duration => .duration

theorem fieldsF_any {ks ats} : (l : List (Attr × QualifiedType)) → FieldsF false false false false ks ats l
  | [] => .nil
  | (_, .required t) :: l => .req _ _ _ (tyF_any t) (fieldsF_any l)
  | (_, .optional t) :: l => .opt _ _ _ (tyF_any t) (fieldsF_any l)

end

/-! ## Records -/

theorem RecTyF.tyF {m d i c ks ats attrs} (h : RecTyF m d i c ks ats attrs) :
    TyF m d i c ks ats (.record (Map.mk attrs)) := by
  cases h
  case mk h₁ h₂ => exact .record _ _ h₁ h₂

theorem TyF.recTyF {m d i c ks ats attrs} (h : TyF m d i c ks ats (.record (Map.mk attrs))) :
    RecTyF m d i c ks ats attrs := by
  cases h
  case record h₁ h₂ => exact .mk _ _ h₁ h₂

theorem recTyF_nil {m d i c ks ats} : RecTyF m d i c ks ats [] := by
  refine .mk [] [] .nil ?_
  cases c <;> cases m
  · exact .rawFF _
  · exact .rawFT _
  · exact .dedupTF _
  · exact .sortTT _

end Cedar.Validation.Relational.SchemaGen
