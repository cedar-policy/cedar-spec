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

module

public import Cedar.Thm.Validation.Relational.Soundness
import Batteries.Data.List.Lemmas
import all Cedar.Data.List -- unfolds `canonicalize`, `insertCanonical`
import all Cedar.Data.Map -- unfolds `keys`, `make`
import all Cedar.Data.Set -- unfolds `any`, `make`, `map`
import all Cedar.Spec.Value -- unfolds `Attr`, `EntityType`
import all Cedar.Validation.Typechecker -- unfolds `Capabilities`, `typeOf`
import all Cedar.Validation.TypedExpr -- unfolds `typeOf`
import all Cedar.Validation.Types -- unfolds `ActionSchema`, `EntitySchema`, `QualifiedType`, …
import all Cedar.Validation.Validator -- unfolds `checkEntities`

/-! # The strictness flags of `HasType`

`HasType` is monotone in both flags (`HasType.mono`); `HasType true true` guarantees the syntactic
conditions (`HasType.strict_syntax`), and conversely (`HasType.strengthen`). -/

@[expose] public section

namespace Cedar.Validation.Relational

open Cedar.Spec Cedar.Data Cedar.Validation

/-! ## The flag-indexed helpers -/

theorem IsTargetOf.mono {b b' : Bool} {env : TypeEnv} {T : EntityType}
    (hb : b' = true → b = true) (h : IsTargetOf b env T) : IsTargetOf b' env T := by
  cases h with
  | strict _ _ _ hv => exact .strict _ _ _ hv
  | lax =>
    cases b' with
    | false => exact .lax _ _
    | true => nomatch hb rfl

theorem DeclIf.mono {b b' : Bool} {ets : EntitySchema} {acts : ActionSchema} {x : Expr}
    (hb : b' = true → b = true) (h : DeclIf b ets acts x) : DeclIf b' ets acts x := by
  cases h with
  | yes _ _ _ _ hd => exact .yes _ _ _ _ hd
  | no =>
    cases b' with
    | false => exact .no _ _ _
    | true => nomatch hb rfl

theorem ParserImageIf.mono {b b' : Bool} {x : Expr}
    (hb : b' = true → b = true) (h : ParserImageIf b x) : ParserImageIf b' x := by
  cases h with
  | yes _ _ hd => exact .yes _ _ hd
  | no =>
    cases b' with
    | false => exact .no _
    | true => nomatch hb rfl

theorem ExtHasIf.mono {b b' : Bool} {a : Attr} {as : List Attr}
    (hb : b' = true → b = true) (h : ExtHasIf b a as) : ExtHasIf b' a as := by
  cases h with
  | yes _ _ _ hp => exact .yes _ _ _ hp
  | no =>
    cases b' with
    | false => exact .no _ _
    | true => nomatch hb rfl

theorem DeadOperand.mono {decl syn decl' syn' : Bool} {env : TypeEnv} {x : Expr}
    (hd : decl' = true → decl = true) (hs : syn' = true → syn = true)
    (h : DeadOperand decl syn env x) : DeadOperand decl' syn' env x := by
  cases h with
  | mk hdecl hsyn => exact .mk _ _ (hdecl.mono hd) (hsyn.mono hs)

/-- With both flags off, any expression is an acceptable skipped operand. -/
theorem DeadOperand.lax (env : TypeEnv) (x : Expr) : DeadOperand false false env x :=
  .mk _ _ (.no _ _ _) (.no _)

theorem IsTargetOf.validEntityType {env : TypeEnv} {T : EntityType} (h : IsTargetOf true env T) :
    ValidEntityType T env.ets env.acts := by
  cases h with
  | strict _ _ _ hv => exact hv

theorem DeclIf.entitiesDeclared {ets : EntitySchema} {acts : ActionSchema} {x : Expr}
    (h : DeclIf true ets acts x) : EntitiesDeclared ets acts x := by
  cases h with
  | yes _ _ _ _ hd => exact hd

theorem ParserImageIf.parserImage {x : Expr} (h : ParserImageIf true x) : ParserImage x := by
  cases h with
  | yes _ _ hd => exact hd

theorem ExtHasIf.parsed {a : Attr} {as : List Attr} (h : ExtHasIf true a as) :
    extHasAttrsParsed a as = true := by
  cases h with
  | yes _ _ _ hp => exact hp

/-! ## Monotonicity -/

/-- **Monotonicity of `HasType` in its flags.** A derivation remains one when either flag is
    cleared. -/
theorem HasType.mono {decl syn decl' syn' : Bool}
    (hd : decl' = true → decl = true) (hs : syn' = true → syn = true)
    {x : Expr} {c : Capabilities} {env : TypeEnv} {ty : CedarType} {cout : Capabilities}
    (h : HasType decl syn x c env ty cout) : HasType decl' syn' x c env ty cout := by
  induction h using HasType.rec
    (motive_2 := fun xs c env tys _ => HasTypeList decl' syn' xs c env tys)
    (motive_3 := fun lb axs c env atys _ => HasTypeRecord decl' syn' lb axs c env atys)
    (motive_4 := fun f args c env t _ => HasTypeExtCall decl' syn' f args c env t)
    (motive_5 := fun b axs c env rty _ => ∀ b', (b' = true → b = true) →
      RecordTypeOf decl' syn' b' axs c env rty)
    (motive_6 := fun axs c env atys _ => HasTypeFields decl' syn' axs c env atys)
    with
  -- The rules whose premises mention a flag.
  | unaryAppIsTrue _ _ _ _ ht _ ih => exact .unaryAppIsTrue _ _ _ _ (ht.mono hd) ih
  | unaryAppIsFalse _ _ _ _ _ hv ht hne _ ih =>
    exact .unaryAppIsFalse _ _ _ _ _ hv (ht.mono hd) hne ih
  | iteTt _ _ _ _ _ _ _ _ _ _ _ hm₁ _ hm₂ hdo ih₁ ih₂ =>
    exact .iteTt _ _ _ _ _ _ _ _ _ _ ih₁ hm₁ ih₂ hm₂ (hdo.mono hd hs)
  | iteAnyBool _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm₁ _ _ hl hm₂ ih₁ ih₂ ih₃ =>
    exact .iteAnyBool _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ hm₁ ih₂ ih₃ hl hm₂
  | iteFf _ _ _ _ _ _ _ _ _ _ hdo ih₁ ih₃ => exact .iteFf _ _ _ _ _ _ _ _ ih₁ ih₃ (hdo.mono hd hs)
  | andShort _ _ _ _ _ _ hdo ih => exact .andShort _ _ _ _ _ ih (hdo.mono hd hs)
  | orShort _ _ _ _ _ _ hdo ih => exact .orShort _ _ _ _ _ ih (hdo.mono hd hs)
  | extHasAttr _ _ _ _ _ _ _ _ _ _ hch hx ih => exact .extHasAttr _ _ _ _ _ _ _ _ _ ih hch (hx.mono hs)
  | record _ _ _ _ _ ih => exact .record _ _ _ _ (ih _ hs)
  | sorted _ _ _ _ _ _ hsort _ ih => exact .sorted _ _ _ _ _ _ hsort ih
  | lax _ _ _ _ _ ih =>
    rename_i b' hb
    cases b' with
    | false => exact .lax _ _ _ _ ih
    | true => nomatch hb rfl
  -- Every other rule: the same rule, with each premise replaced by its induction hypothesis.
  | _ =>
    intros
    first
    | (apply HasType.litBoolTrue; solve_by_elim*)
    | (apply HasType.litBoolFalse; solve_by_elim*)
    | (apply HasType.litInt; solve_by_elim*)
    | (apply HasType.litString; solve_by_elim*)
    | (apply HasType.litEntity; solve_by_elim*)
    | (apply HasType.varPrincipal; solve_by_elim*)
    | (apply HasType.varAction; solve_by_elim*)
    | (apply HasType.varResource; solve_by_elim*)
    | (apply HasType.varContext; solve_by_elim*)
    | (apply HasType.unaryAppNotTt; solve_by_elim*)
    | (apply HasType.unaryAppNotFf; solve_by_elim*)
    | (apply HasType.unaryAppNotAny; solve_by_elim*)
    | (apply HasType.unaryAppNeg; solve_by_elim*)
    | (apply HasType.unaryAppIsEmpty; solve_by_elim*)
    | (apply HasType.unaryAppLike; solve_by_elim*)
    | (apply HasType.binaryAppEqLitSame; solve_by_elim*)
    | (apply HasType.binaryAppEqLitDiff; solve_by_elim*)
    | (apply HasType.binaryAppEqNonLitLub; solve_by_elim*)
    | (apply HasType.binaryAppEqEntityDiff; solve_by_elim*)
    | (apply HasType.binaryAppLessInt; solve_by_elim*)
    | (apply HasType.binaryAppLessDatetime; solve_by_elim*)
    | (apply HasType.binaryAppLessDuration; solve_by_elim*)
    | (apply HasType.binaryAppLessEqInt; solve_by_elim*)
    | (apply HasType.binaryAppLessEqDatetime; solve_by_elim*)
    | (apply HasType.binaryAppLessEqDuration; solve_by_elim*)
    | (apply HasType.binaryAppAdd; solve_by_elim*)
    | (apply HasType.binaryAppSub; solve_by_elim*)
    | (apply HasType.binaryAppMul; solve_by_elim*)
    | (apply HasType.binaryAppContains; solve_by_elim*)
    | (apply HasType.binaryAppContainsAll; solve_by_elim*)
    | (apply HasType.binaryAppContainsAny; solve_by_elim*)
    | (apply HasType.binaryAppMemEntityEntity; solve_by_elim*)
    | (apply HasType.binaryAppMemEntitySame; solve_by_elim*)
    | (apply HasType.binaryAppMemEntitySet; solve_by_elim*)
    | (apply HasType.binaryAppMemEntityEntityFf; solve_by_elim*)
    | (apply HasType.binaryAppMemEntitySetFf; solve_by_elim*)
    | (apply HasType.binaryAppMemActionEntityFf; solve_by_elim*)
    | (apply HasType.binaryAppMemActionSetFf; solve_by_elim*)
    | (apply HasType.binaryAppMemActionLitTt; solve_by_elim*)
    | (apply HasType.binaryAppMemActionLitFf; solve_by_elim*)
    | (apply HasType.binaryAppMemActionLitSetTt; solve_by_elim*)
    | (apply HasType.binaryAppMemActionLitSetFf; solve_by_elim*)
    | (apply HasType.hasAttrRecord; solve_by_elim*)
    | (apply HasType.hasAttrRecordNotFound; solve_by_elim*)
    | (apply HasType.hasAttrEntity; solve_by_elim*)
    | (apply HasType.hasAttrEntityNotFound; solve_by_elim*)
    | (apply HasType.hasAttrEnum; solve_by_elim*)
    | (apply HasType.hasAttrActionFf; solve_by_elim*)
    | (apply HasType.getAttrRecord; solve_by_elim*)
    | (apply HasType.getAttrEntity; solve_by_elim*)
    | (apply HasType.hasTagAnyBool; solve_by_elim*)
    | (apply HasType.hasTagTt; solve_by_elim*)
    | (apply HasType.hasTagFf; solve_by_elim*)
    | (apply HasType.hasTagActionFf; solve_by_elim*)
    | (apply HasType.getTag; solve_by_elim*)
    | (apply HasType.andTtFf; solve_by_elim*)
    | (apply HasType.andTtTt; solve_by_elim*)
    | (apply HasType.andTtAny; solve_by_elim*)
    | (apply HasType.andAnyFf; solve_by_elim*)
    | (apply HasType.andAnyTt; solve_by_elim*)
    | (apply HasType.andAnyAny; solve_by_elim*)
    | (apply HasType.orFfThen; solve_by_elim*)
    | (apply HasType.orAnyTt; solve_by_elim*)
    | (apply HasType.orAnyFf; solve_by_elim*)
    | (apply HasType.orAnyAny; solve_by_elim*)
    | (apply HasType.set; solve_by_elim*)
    | (apply HasType.callExt; solve_by_elim*)
    | (apply HasTypeList.nil; solve_by_elim*)
    | (apply HasTypeList.cons; solve_by_elim*)
    | (apply HasTypeRecord.nil; solve_by_elim*)
    | (apply HasTypeRecord.cons; solve_by_elim*)
    | (apply HasTypeExtCall.decimal; solve_by_elim*)
    | (apply HasTypeExtCall.ip; solve_by_elim*)
    | (apply HasTypeExtCall.datetime; solve_by_elim*)
    | (apply HasTypeExtCall.duration; solve_by_elim*)
    | (apply HasTypeExtCall.lessThan; solve_by_elim*)
    | (apply HasTypeExtCall.lessThanOrEqual; solve_by_elim*)
    | (apply HasTypeExtCall.greaterThan; solve_by_elim*)
    | (apply HasTypeExtCall.greaterThanOrEqual; solve_by_elim*)
    | (apply HasTypeExtCall.isIpv4; solve_by_elim*)
    | (apply HasTypeExtCall.isIpv6; solve_by_elim*)
    | (apply HasTypeExtCall.isLoopback; solve_by_elim*)
    | (apply HasTypeExtCall.isMulticast; solve_by_elim*)
    | (apply HasTypeExtCall.isInRange; solve_by_elim*)
    | (apply HasTypeExtCall.offset; solve_by_elim*)
    | (apply HasTypeExtCall.durationSince; solve_by_elim*)
    | (apply HasTypeExtCall.toDate; solve_by_elim*)
    | (apply HasTypeExtCall.toTime; solve_by_elim*)
    | (apply HasTypeExtCall.toMilliseconds; solve_by_elim*)
    | (apply HasTypeExtCall.toSeconds; solve_by_elim*)
    | (apply HasTypeExtCall.toMinutes; solve_by_elim*)
    | (apply HasTypeExtCall.toHours; solve_by_elim*)
    | (apply HasTypeExtCall.toDays; solve_by_elim*)
    | (apply HasTypeFields.nil; solve_by_elim*)
    | (apply HasTypeFields.cons; solve_by_elim*)

/-- A derivation with any flags is one of `HasType false false`, i.e. of `typeOf`. -/
theorem HasType.weaken {decl syn : Bool} {x : Expr} {c : Capabilities} {env : TypeEnv}
    {ty : CedarType} {cout : Capabilities} (h : HasType decl syn x c env ty cout) :
    HasType false false x c env ty cout :=
  HasType.mono (decl' := false) (syn' := false) (fun h => nomatch h) (fun h => nomatch h) h

/-! ## The syntactic conditions -/

theorem DeadOperand.entitiesDeclared {syn : Bool} {env : TypeEnv} {x : Expr}
    (h : DeadOperand true syn env x) : EntitiesDeclared env.ets env.acts x := by
  cases h with
  | mk hdecl _ => exact hdecl.entitiesDeclared

theorem DeadOperand.parserImage {decl : Bool} {env : TypeEnv} {x : Expr}
    (h : DeadOperand decl true env x) : ParserImage x := by
  cases h with
  | mk _ hsyn => exact hsyn.parserImage

/-- Inserting a field only adds it. -/
theorem InsertSortedField.perm {ax : Attr × Expr} {axs axs' : List (Attr × Expr)}
    (h : InsertSortedField ax axs axs') : axs'.Perm (ax :: axs) := by
  induction h with
  | nil | here => exact .refl _
  | there a x a' x' _ _ _ _ ih => exact (ih.cons _).trans (.swap _ _ _)

/-- Sorting only rearranges the fields. -/
theorem SortsTo.perm {axs axs' : List (Attr × Expr)} (h : SortsTo axs axs') : axs'.Perm axs := by
  induction h with
  | nil => exact .refl _
  | cons ax _ _ _ _ hins ih => exact hins.perm.trans (ih.cons ax)

theorem nodup_keys_of_sortedBy {l : List (Attr × Expr)} (h : List.SortedBy Prod.fst l) :
    (l.map Prod.fst).Nodup := by
  induction l with
  | nil => exact .nil
  | cons hd tl ih =>
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih (List.tail_sortedBy h)⟩
    obtain ⟨ax, hax, hk⟩ := List.mem_map.mp hmem
    have hlt := List.sortedBy_implies_head_lt_tail h ax hax
    rw [hk] at hlt
    exact StrictLT.irreflexive _ hlt

/-- A record literal that sorts (`SortsTo`) has distinct keys. -/
theorem SortsTo.nodup_keys {axs axs' : List (Attr × Expr)} (h : SortsTo axs axs') :
    (axs.map Prod.fst).Nodup := by
  have hsorted := sortsTo_canonicalize h ▸ List.canonicalize_sortedBy Prod.fst axs
  exact ((h.perm.map Prod.fst).nodup_iff).mp (nodup_keys_of_sortedBy hsorted)

theorem entitiesDeclaredRecord_iff {ets : EntitySchema} {acts : ActionSchema} :
    ∀ {axs : List (Attr × Expr)},
      EntitiesDeclaredRecord ets acts axs ↔ ∀ ax ∈ axs, EntitiesDeclared ets acts ax.2
  | [] => ⟨fun _ _ h => (nomatch h), fun _ => EntitiesDeclaredRecord.nil _ _⟩
  | (a, x) :: axs => by
    rw [List.forall_mem_cons, ← entitiesDeclaredRecord_iff]
    constructor
    · intro h; cases h; constructor <;> assumption
    · rintro ⟨hx, hr⟩; exact .cons _ _ _ _ _ hx hr

/-- **Declared entities.** A derivation with the `decl` flag set types only expressions whose
    entity literals are valid and whose `is` targets are declared (`checkEntities` succeeds):
    typed entity literals are valid by `litEntity`, `is` targets by `IsTargetOf true`, and
    skipped operands by `DeadOperand true`. -/
theorem HasType.entitiesDeclared {syn : Bool} {x : Expr} {c : Capabilities} {env : TypeEnv}
    {ty : CedarType} {cout : Capabilities} (h : HasType true syn x c env ty cout) :
    EntitiesDeclared env.ets env.acts x := by
  induction h using HasType.rec
    (motive_2 := fun xs _ env _ _ => EntitiesDeclaredList env.ets env.acts xs)
    (motive_3 := fun _ axs _ env _ _ => ∀ ax ∈ axs, EntitiesDeclared env.ets env.acts ax.2)
    (motive_4 := fun _ args _ env _ _ => EntitiesDeclaredList env.ets env.acts args)
    (motive_5 := fun _ axs _ env _ _ => ∀ ax ∈ axs, EntitiesDeclared env.ets env.acts ax.2)
    (motive_6 := fun axs _ env _ _ => ∀ ax ∈ axs, EntitiesDeclared env.ets env.acts ax.2)
    with
  | unaryAppIsTrue _ _ _ _ ht _ ih => exact .is _ _ _ _ ht.validEntityType ih
  | unaryAppIsFalse _ _ _ _ _ _ ht _ _ ih => exact .is _ _ _ _ ht.validEntityType ih
  | iteTt _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdo ih₁ ih₂ =>
    exact .ite _ _ _ _ _ ih₁ ih₂ hdo.entitiesDeclared
  | iteFf _ _ _ _ _ _ _ _ _ _ hdo ih₁ ih₃ => exact .ite _ _ _ _ _ ih₁ hdo.entitiesDeclared ih₃
  | andShort _ _ _ _ _ _ hdo ih => exact .and _ _ _ _ ih hdo.entitiesDeclared
  | orShort _ _ _ _ _ _ hdo ih => exact .or _ _ _ _ ih hdo.entitiesDeclared
  | record _ _ _ _ _ ih => exact .record _ _ _ (entitiesDeclaredRecord_iff.mpr ih)
  | sorted _ _ _ _ _ _ hsort _ ih =>
    rename_i ax hax
    exact ih ax (hsort.perm.mem_iff.mpr hax)
  | lax _ _ _ _ _ ih =>
    rename_i ax hax
    exact ih ax hax
  | _ =>
    intros
    first
    | (repeat' (first | assumption | constructor)); done
    | (rename_i y hy
       revert y hy
       simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true]
       repeat' (first | assumption | constructor)); done

/-- **The parser's image.** A derivation with the `syn` flag set types only expressions in the
    image of the parser: typed record literals have distinct keys by `RecordTypeOf.sorted`,
    typed extended `has` paths are identifiers by `ExtHasIf`, and skipped operands are covered
    by `DeadOperand`. -/
theorem HasType.parserImage {decl : Bool} {x : Expr} {c : Capabilities} {env : TypeEnv}
    {ty : CedarType} {cout : Capabilities} (h : HasType decl true x c env ty cout) :
    ParserImage x := by
  induction h using HasType.rec
    (motive_2 := fun xs _ _ _ _ => ∀ x ∈ xs, ParserImage x)
    (motive_3 := fun _ axs _ _ _ _ => ∀ ax ∈ axs, ParserImage ax.2)
    (motive_4 := fun _ args _ _ _ _ => ∀ x ∈ args, ParserImage x)
    (motive_5 := fun b axs _ _ _ _ =>
      (b = true → (axs.map Prod.fst).Nodup) ∧ ∀ ax ∈ axs, ParserImage ax.2)
    (motive_6 := fun axs _ _ _ _ => ∀ ax ∈ axs, ParserImage ax.2)
    with
  | iteTt _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdo ih₁ ih₂ =>
    exact .ite _ _ _ ih₁ ih₂ hdo.parserImage
  | iteFf _ _ _ _ _ _ _ _ _ _ hdo ih₁ ih₃ => exact .ite _ _ _ ih₁ hdo.parserImage ih₃
  | andShort _ _ _ _ _ _ hdo ih => exact .and _ _ ih hdo.parserImage
  | orShort _ _ _ _ _ _ hdo ih => exact .or _ _ ih hdo.parserImage
  | set _ _ _ _ _ _ _ _ _ _ ih ihs => exact .set _ (List.forall_mem_cons.mpr ⟨ih, ihs⟩)
  | record _ _ _ _ _ ih =>
    refine .record _ (ih.1 rfl) (fun x hx => ?_)
    obtain ⟨ax, hax, rfl⟩ := List.mem_map.mp hx
    exact ih.2 ax hax
  | extHasAttr _ _ _ _ _ _ _ _ _ _ _ hx ih => exact .extHasAttr _ _ _ hx.parsed ih
  | callExt _ _ _ _ _ _ ih => exact .call _ _ ih
  | sorted _ _ _ _ _ _ hsort _ ih =>
    exact ⟨fun _ => hsort.nodup_keys, fun ax hax => ih ax (hsort.perm.mem_iff.mpr hax)⟩
  | lax _ _ _ _ _ ih => exact ⟨fun h => (nomatch h), ih⟩
  | _ =>
    intros
    first
    | (repeat' (first | assumption | constructor)); done
    | (rename_i y hy
       revert y hy
       simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
       repeat' (first | assumption | constructor)); done

/-- **Strict derivations meet the syntactic conditions.** An expression typed by
    `HasType true true` has declared entities and is in the parser's image, the two conditions
    beyond `typeOf` that a validated, parsed policy meets. -/
theorem HasType.strict_syntax {x : Expr} {c : Capabilities} {env : TypeEnv} {ty : CedarType}
    {cout : Capabilities} (h : HasType true true x c env ty cout) :
    EntitiesDeclared env.ets env.acts x ∧ ParserImage x :=
  ⟨h.entitiesDeclared, h.parserImage⟩

/-! ## Strengthening -/

/-- Inserting an attribute by key into the typed attributes of a literal types the literal with
    the attribute inserted, with `List.insertCanonical` on the attribute types. -/
theorem HasTypeFields.insertSortedField {decl syn : Bool} {ax : Attr × Expr}
    {axs axs' : List (Attr × Expr)} {c : Capabilities} {env : TypeEnv} {ty : CedarType}
    {oc : Capabilities} (hins : InsertSortedField ax axs axs')
    (hx : HasType decl syn ax.2 c env ty oc) :
    ∀ {atys}, HasTypeFields decl syn axs c env atys →
      HasTypeFields decl syn axs' c env
        (List.insertCanonical Prod.fst (ax.1, .required ty) atys) := by
  induction hins with
  | nil a x =>
    intro atys h
    cases h
    exact .cons _ _ _ _ _ _ _ hx (.nil _ _)
  | here a x a' x' axs hlt =>
    intro atys h
    cases h with
    | cons _ _ _ _ _ ty' atys' hx' h' =>
      simp only [List.insertCanonical, hlt, ↓reduceIte]
      exact .cons _ _ _ _ _ _ _ hx (.cons _ _ _ _ _ _ _ hx' h')
  | there a x a' x' axs axs' hlt _ ih =>
    intro atys h
    cases h with
    | cons _ _ _ _ _ ty' atys' hx' h' =>
      simp only [List.insertCanonical, StrictLT.asymmetric a' a hlt, hlt, ↓reduceIte]
      exact .cons _ _ _ _ _ _ _ hx' (ih hx h')

/-- Typing the attributes of a record literal in source order types them in key order too, with
    the attribute types canonicalized (`List.canonicalize`), as `Map.make` does. -/
theorem HasTypeFields.sortsTo {decl syn : Bool} {axs axs' : List (Attr × Expr)}
    {c : Capabilities} {env : TypeEnv} (hsort : SortsTo axs axs') :
    ∀ {atys}, HasTypeFields decl syn axs c env atys →
      HasTypeFields decl syn axs' c env (List.canonicalize Prod.fst atys) := by
  induction hsort with
  | nil => intro atys h; cases h; exact .nil _ _
  | cons ax axs axs' axs'' _ hins ih =>
    intro atys h
    obtain ⟨a, x⟩ := ax
    cases h with
    | cons _ _ _ _ _ ty atys' hx h' => exact (ih h').insertSortedField hins hx

/-- Attributes typed in strictly increasing key order are typed by `HasTypeRecord`. -/
theorem HasTypeFields.hasTypeRecord {decl syn : Bool} {c : Capabilities} {env : TypeEnv} :
    ∀ {axs : List (Attr × Expr)} {atys : List (Attr × QualifiedType)} {lb : Option Attr},
      HasTypeFields decl syn axs c env atys → (∀ ax ∈ axs, KeyAbove lb ax.1) →
      List.SortedBy Prod.fst axs → HasTypeRecord decl syn lb axs c env atys
  | [], _, _, h, _, _ => by cases h; exact .nil _ _ _
  | (a, x) :: axs, _, lb, h, hka, hsorted => by
    cases h with
    | cons _ _ _ _ _ ty atys hx h' =>
      exact .cons _ _ _ _ _ _ _ _ (hka (a, x) List.mem_cons_self) hx
        (h'.hasTypeRecord
          (fun ax hax => .some a ax.1 (List.sortedBy_implies_head_lt_tail hsorted ax hax))
          (List.tail_sortedBy hsorted))

/-- An attribute whose key is not in the list can be inserted into it. -/
theorem insertSortedField_exists {a : Attr} {x : Expr} :
    ∀ {axs : List (Attr × Expr)}, a ∉ axs.map Prod.fst → ∃ axs', InsertSortedField (a, x) axs axs'
  | [], _ => ⟨_, .nil a x⟩
  | (a', x') :: axs, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rcases StrictLT.connected a a' h.1 with hlt | hlt
    · exact ⟨_, .here a x a' x' axs hlt⟩
    · obtain ⟨axs', hins⟩ := insertSortedField_exists (x := x) h.2
      exact ⟨_, .there a x a' x' axs axs' hlt hins⟩

/-- A record literal with distinct keys can be sorted. -/
theorem sortsTo_of_nodup :
    ∀ {axs : List (Attr × Expr)}, (axs.map Prod.fst).Nodup → ∃ axs', SortsTo axs axs'
  | [], _ => ⟨[], .nil⟩
  | (a, x) :: axs, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    obtain ⟨axs', hs⟩ := sortsTo_of_nodup h.2
    have hnot : a ∉ axs'.map Prod.fst := fun hmem => h.1 ((hs.perm.map Prod.fst).mem_iff.mp hmem)
    obtain ⟨axs'', hins⟩ := insertSortedField_exists (x := x) hnot
    exact ⟨axs'', .cons _ _ _ _ hs hins⟩

/-- With distinct keys, the `lax` record rule is an instance of the `sorted` one. -/
theorem HasTypeFields.recordTypeOf_sorted {decl syn b : Bool} {axs : List (Attr × Expr)}
    {c : Capabilities} {env : TypeEnv} {atys : List (Attr × QualifiedType)}
    (h : HasTypeFields decl syn axs c env atys) (hnd : (axs.map Prod.fst).Nodup) :
    RecordTypeOf decl syn b axs c env (Map.make atys) := by
  obtain ⟨axs', hsort⟩ := sortsTo_of_nodup hnd
  have hsorted := sortsTo_canonicalize hsort ▸ List.canonicalize_sortedBy Prod.fst axs
  exact .sorted _ _ _ _ _ _ hsort
    ((h.sortsTo hsort).hasTypeRecord (fun ax _ => .none ax.1) hsorted)

/-- A skipped operand meeting both syntactic conditions is acceptable with both flags set. -/
theorem DeadOperand.strict {env : TypeEnv} {x : Expr} (hd : EntitiesDeclared env.ets env.acts x)
    (hk : ParserImage x) : DeadOperand true true env x :=
  .mk _ _ (.yes _ _ _ _ hd) (.yes _ _ hk)

open Lean Elab Tactic in
/-- Applies the rule an induction case is named after: in the case of rule `r`, the goal
    `I …` (for one of the inductives `I` of the typing relation) is refined by `apply I.r`,
    leaving the premises of the rule. -/
local elab "apply_case_rule" : tactic => do
  let g ← getMainGoal
  let some I := (← instantiateMVars (← g.getType)).getAppFn.constName?
    | throwError "apply_case_rule: the goal is not an application of an inductive"
  let rule := mkIdent (I ++ (← g.getTag).getRoot)
  evalTactic (← `(tactic| apply $rule))

/-- Closes the premises of a typing rule from the context, the induction hypotheses, and the
    syntactic conditions on the subexpressions. -/
local macro "premises" : tactic =>
  `(tactic| first | done | solve_by_elim* (maxDepth := 16) [IsTargetOf.strict, DeadOperand.strict, ExtHasIf.yes])

/-- A `HasType false false` derivation of an expression with declared entities, in the parser's
    image, is a `HasType true true` derivation. -/
theorem HasType.strengthen {x : Expr} {c : Capabilities} {env : TypeEnv} {ty : CedarType}
    {cout : Capabilities} (h : HasType false false x c env ty cout)
    (hd : EntitiesDeclared env.ets env.acts x) (hk : ParserImage x) :
    HasType true true x c env ty cout := by
  revert hd hk
  induction h using HasType.rec
    (motive_2 := fun xs c env tys _ => EntitiesDeclaredList env.ets env.acts xs →
      (∀ x ∈ xs, ParserImage x) → HasTypeList true true xs c env tys)
    (motive_3 := fun lb axs c env atys _ => (∀ ax ∈ axs, EntitiesDeclared env.ets env.acts ax.2) →
      (∀ ax ∈ axs, ParserImage ax.2) → HasTypeRecord true true lb axs c env atys)
    (motive_4 := fun f args c env t _ => EntitiesDeclaredList env.ets env.acts args →
      (∀ x ∈ args, ParserImage x) → HasTypeExtCall true true f args c env t)
    (motive_5 := fun _ axs c env rty _ => (∀ ax ∈ axs, EntitiesDeclared env.ets env.acts ax.2) →
      (axs.map Prod.fst).Nodup → (∀ ax ∈ axs, ParserImage ax.2) →
      RecordTypeOf true true true axs c env rty)
    (motive_6 := fun axs c env atys _ => (∀ ax ∈ axs, EntitiesDeclared env.ets env.acts ax.2) →
      (∀ ax ∈ axs, ParserImage ax.2) → HasTypeFields true true axs c env atys)
    with
  -- The record rules, whose premises are about attribute lists.
  | record _ _ _ _ _ ih =>
    intro hd hk
    cases hd with
    | record _ hd₁ =>
      cases hk with
      | record _ hnd hk₁ =>
        exact .record _ _ _ _ (ih (entitiesDeclaredRecord_iff.mp hd₁) hnd
          (fun ax hax => hk₁ ax.2 (List.mem_map_of_mem hax)))
  | sorted _ _ _ _ _ _ hsort _ ih =>
    rename_i hd _ hk
    exact .sorted _ _ _ _ _ _ hsort (ih (fun ax hax => hd ax (hsort.perm.mem_iff.mp hax))
      (fun ax hax => hk ax (hsort.perm.mem_iff.mp hax)))
  | lax _ _ _ _ _ ih =>
    rename_i hd hnd hk
    exact (ih hd hk).recordTypeOf_sorted hnd
  -- Every other rule: the same rule, with each premise replaced by its induction hypothesis.
  | _ =>
    intros
    (try cases ‹EntitiesDeclared _ _ _›); (try cases ‹ParserImage _›)
    try simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true] at *
    repeat (first | cases ‹_ ∧ _› | cases ‹EntitiesDeclaredList _ _ (_ :: _)›)
    apply_case_rule
    premises

end Cedar.Validation.Relational
