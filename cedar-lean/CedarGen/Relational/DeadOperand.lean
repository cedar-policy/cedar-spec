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

import CedarGen.Relational.Decidables

/-! # Dead operands

`DeadOperand decl syn env x`: an operand `typeOf` skips (an untaken `if` branch, the right operand of
a short-circuited `&&`/`||`). It need not be well typed, only meet the syntactic conditions the flags
select. Its producer, in `Instances`, draws small literals and variables, and otherwise any expression
meeting them, so an ill-typed one tests that the validator skips it. -/

namespace Cedar.Validation.Relational

open Cedar.Spec Cedar.Data Cedar.Validation

/-! ## Deciding the conditions -/

mutual
/-- `EntitiesDeclared ets acts x`, decided. -/
def entitiesDeclaredB (ets : EntitySchema) (acts : ActionSchema) : Expr → Bool
  | .lit (.entityUID ⟨ety, eid⟩) => decide (ValidEntityUID ety eid ets acts)
  | .lit _ => true
  | .var _ => true
  | .ite a b c => entitiesDeclaredB ets acts a && entitiesDeclaredB ets acts b && entitiesDeclaredB ets acts c
  | .and a b => entitiesDeclaredB ets acts a && entitiesDeclaredB ets acts b
  | .or a b => entitiesDeclaredB ets acts a && entitiesDeclaredB ets acts b
  | .unaryApp (.is ety) a => decide (ValidEntityType ety ets acts) && entitiesDeclaredB ets acts a
  | .unaryApp _ a => entitiesDeclaredB ets acts a
  | .binaryApp _ a b => entitiesDeclaredB ets acts a && entitiesDeclaredB ets acts b
  | .getAttr a _ => entitiesDeclaredB ets acts a
  | .hasAttr a _ => entitiesDeclaredB ets acts a
  | .extHasAttr a _ _ => entitiesDeclaredB ets acts a
  | .set xs => entitiesDeclaredListB ets acts xs
  | .record axs => entitiesDeclaredRecordB ets acts axs
  | .call _ xs => entitiesDeclaredListB ets acts xs

/-- `EntitiesDeclaredList`, decided. -/
def entitiesDeclaredListB (ets : EntitySchema) (acts : ActionSchema) : List Expr → Bool
  | [] => true
  | x :: xs => entitiesDeclaredB ets acts x && entitiesDeclaredListB ets acts xs

/-- `EntitiesDeclaredRecord`, decided. -/
def entitiesDeclaredRecordB (ets : EntitySchema) (acts : ActionSchema) : List (Attr × Expr) → Bool
  | [] => true
  | (_, x) :: axs => entitiesDeclaredB ets acts x && entitiesDeclaredRecordB ets acts axs
end

mutual
theorem entitiesDeclared_of_B {ets : EntitySchema} {acts : ActionSchema} :
    ∀ (x : Expr), entitiesDeclaredB ets acts x = true → EntitiesDeclared ets acts x
  | .lit (.entityUID ⟨ety, eid⟩), h => .litEntity _ _ _ _ (of_decide_eq_true h)
  | .lit (.bool _), _ => .litBool _ _ _
  | .lit (.int _), _ => .litInt _ _ _
  | .lit (.string _), _ => .litString _ _ _
  | .var _, _ => .var _ _ _
  | .ite a b c, h => by
    simp only [entitiesDeclaredB, Bool.and_eq_true] at h
    exact .ite _ _ _ _ _ (entitiesDeclared_of_B a h.1.1) (entitiesDeclared_of_B b h.1.2)
      (entitiesDeclared_of_B c h.2)
  | .and a b, h => by
    simp only [entitiesDeclaredB, Bool.and_eq_true] at h
    exact .and _ _ _ _ (entitiesDeclared_of_B a h.1) (entitiesDeclared_of_B b h.2)
  | .or a b, h => by
    simp only [entitiesDeclaredB, Bool.and_eq_true] at h
    exact .or _ _ _ _ (entitiesDeclared_of_B a h.1) (entitiesDeclared_of_B b h.2)
  | .unaryApp (.is ety) a, h => by
    simp only [entitiesDeclaredB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .is _ _ _ _ h.1 (entitiesDeclared_of_B a h.2)
  | .unaryApp .not a, h => .not _ _ _ (entitiesDeclared_of_B a h)
  | .unaryApp .neg a, h => .neg _ _ _ (entitiesDeclared_of_B a h)
  | .unaryApp .isEmpty a, h => .isEmpty _ _ _ (entitiesDeclared_of_B a h)
  | .unaryApp (.like _) a, h => .like _ _ _ _ (entitiesDeclared_of_B a h)
  | .binaryApp _ a b, h => by
    simp only [entitiesDeclaredB, Bool.and_eq_true] at h
    exact .binaryApp _ _ _ _ _ (entitiesDeclared_of_B a h.1) (entitiesDeclared_of_B b h.2)
  | .getAttr a _, h => .getAttr _ _ _ _ (entitiesDeclared_of_B a h)
  | .hasAttr a _, h => .hasAttr _ _ _ _ (entitiesDeclared_of_B a h)
  | .extHasAttr a _ _, h => .extHasAttr _ _ _ _ _ (entitiesDeclared_of_B a h)
  | .set xs, h => .set _ _ _ (entitiesDeclaredList_of_B xs h)
  | .record axs, h => .record _ _ _ (entitiesDeclaredRecord_of_B axs h)
  | .call _ xs, h => .call _ _ _ _ (entitiesDeclaredList_of_B xs h)

theorem entitiesDeclaredList_of_B {ets : EntitySchema} {acts : ActionSchema} :
    ∀ (xs : List Expr), entitiesDeclaredListB ets acts xs = true → EntitiesDeclaredList ets acts xs
  | [], _ => .nil _ _
  | x :: xs, h => by
    simp only [entitiesDeclaredListB, Bool.and_eq_true] at h
    exact .cons _ _ _ _ (entitiesDeclared_of_B x h.1) (entitiesDeclaredList_of_B xs h.2)

theorem entitiesDeclaredRecord_of_B {ets : EntitySchema} {acts : ActionSchema} :
    ∀ (axs : List (Attr × Expr)), entitiesDeclaredRecordB ets acts axs = true →
      EntitiesDeclaredRecord ets acts axs
  | [], _ => .nil _ _
  | (_, x) :: axs, h => by
    simp only [entitiesDeclaredRecordB, Bool.and_eq_true] at h
    exact .cons _ _ _ _ _ (entitiesDeclared_of_B x h.1) (entitiesDeclaredRecord_of_B axs h.2)
end

mutual
theorem entitiesDeclaredB_of {ets : EntitySchema} {acts : ActionSchema} :
    ∀ (x : Expr), EntitiesDeclared ets acts x → entitiesDeclaredB ets acts x = true
  | .lit (.entityUID ⟨ety, eid⟩), h => by
    cases h with
    | litEntity _ _ hv => exact decide_eq_true hv
  | .lit (.bool _), _ => rfl
  | .lit (.int _), _ => rfl
  | .lit (.string _), _ => rfl
  | .var _, _ => rfl
  | .ite a b c, h => by
    cases h with
    | ite _ _ _ ha hb hc =>
      simp only [entitiesDeclaredB, Bool.and_eq_true]
      exact ⟨⟨entitiesDeclaredB_of a ha, entitiesDeclaredB_of b hb⟩, entitiesDeclaredB_of c hc⟩
  | .and a b, h => by
    cases h with
    | and _ _ ha hb =>
      simp only [entitiesDeclaredB, Bool.and_eq_true]
      exact ⟨entitiesDeclaredB_of a ha, entitiesDeclaredB_of b hb⟩
  | .or a b, h => by
    cases h with
    | or _ _ ha hb =>
      simp only [entitiesDeclaredB, Bool.and_eq_true]
      exact ⟨entitiesDeclaredB_of a ha, entitiesDeclaredB_of b hb⟩
  | .unaryApp (.is ety) a, h => by
    cases h with
    | is _ _ hv ha =>
      simp only [entitiesDeclaredB, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hv, entitiesDeclaredB_of a ha⟩
  | .unaryApp .not a, h => by cases h with | not _ ha => exact entitiesDeclaredB_of a ha
  | .unaryApp .neg a, h => by cases h with | neg _ ha => exact entitiesDeclaredB_of a ha
  | .unaryApp .isEmpty a, h => by cases h with | isEmpty _ ha => exact entitiesDeclaredB_of a ha
  | .unaryApp (.like _) a, h => by cases h with | like _ _ ha => exact entitiesDeclaredB_of a ha
  | .binaryApp _ a b, h => by
    cases h with
    | binaryApp _ _ _ ha hb =>
      simp only [entitiesDeclaredB, Bool.and_eq_true]
      exact ⟨entitiesDeclaredB_of a ha, entitiesDeclaredB_of b hb⟩
  | .getAttr a _, h => by cases h with | getAttr _ _ ha => exact entitiesDeclaredB_of a ha
  | .hasAttr a _, h => by cases h with | hasAttr _ _ ha => exact entitiesDeclaredB_of a ha
  | .extHasAttr a _ _, h => by
    cases h with | extHasAttr _ _ _ ha => exact entitiesDeclaredB_of a ha
  | .set xs, h => by cases h with | set _ hs => exact entitiesDeclaredListB_of xs hs
  | .record axs, h => by cases h with | record _ hs => exact entitiesDeclaredRecordB_of axs hs
  | .call _ xs, h => by cases h with | call _ _ hs => exact entitiesDeclaredListB_of xs hs

theorem entitiesDeclaredListB_of {ets : EntitySchema} {acts : ActionSchema} :
    ∀ (xs : List Expr), EntitiesDeclaredList ets acts xs → entitiesDeclaredListB ets acts xs = true
  | [], _ => rfl
  | x :: xs, h => by
    cases h with
    | cons _ _ hx hxs =>
      simp only [entitiesDeclaredListB, Bool.and_eq_true]
      exact ⟨entitiesDeclaredB_of x hx, entitiesDeclaredListB_of xs hxs⟩

theorem entitiesDeclaredRecordB_of {ets : EntitySchema} {acts : ActionSchema} :
    ∀ (axs : List (Attr × Expr)), EntitiesDeclaredRecord ets acts axs →
      entitiesDeclaredRecordB ets acts axs = true
  | [], _ => rfl
  | (_, x) :: axs, h => by
    cases h with
    | cons _ _ _ hx hxs =>
      simp only [entitiesDeclaredRecordB, Bool.and_eq_true]
      exact ⟨entitiesDeclaredB_of x hx, entitiesDeclaredRecordB_of axs hxs⟩
end

mutual
/-- `ParserImage x`, decided. -/
def parserImageB : Expr → Bool
  | .lit _ | .var _ => true
  | .ite a b c => parserImageB a && parserImageB b && parserImageB c
  | .and a b | .or a b | .binaryApp _ a b => parserImageB a && parserImageB b
  | .unaryApp _ a | .getAttr a _ | .hasAttr a _ => parserImageB a
  | .extHasAttr a k ks => extHasAttrsParsed k ks && parserImageB a
  | .set xs | .call _ xs => parserImageListB xs
  | .record axs => decide (axs.map Prod.fst).Nodup && parserImageRecordB axs

/-- `ParserImage` of each expression of a list, decided. -/
def parserImageListB : List Expr → Bool
  | [] => true
  | x :: xs => parserImageB x && parserImageListB xs

/-- `ParserImage` of each field of a record literal, decided. -/
def parserImageRecordB : List (Attr × Expr) → Bool
  | [] => true
  | (_, x) :: axs => parserImageB x && parserImageRecordB axs
end

mutual
theorem parserImage_iff : ∀ (x : Expr), ParserImage x ↔ parserImageB x = true
  | .lit _ => ⟨fun _ => rfl, fun _ => .lit _⟩
  | .var _ => ⟨fun _ => rfl, fun _ => .var _⟩
  | .ite a b c => by
    simp only [parserImageB, Bool.and_eq_true, ← parserImage_iff a, ← parserImage_iff b,
      ← parserImage_iff c]
    exact ⟨fun h => by cases h with | ite _ _ _ ha hb hc => exact ⟨⟨ha, hb⟩, hc⟩,
      fun ⟨⟨ha, hb⟩, hc⟩ => .ite _ _ _ ha hb hc⟩
  | .and a b => by
    simp only [parserImageB, Bool.and_eq_true, ← parserImage_iff a, ← parserImage_iff b]
    exact ⟨fun h => by cases h with | and _ _ ha hb => exact ⟨ha, hb⟩, fun ⟨ha, hb⟩ => .and _ _ ha hb⟩
  | .or a b => by
    simp only [parserImageB, Bool.and_eq_true, ← parserImage_iff a, ← parserImage_iff b]
    exact ⟨fun h => by cases h with | or _ _ ha hb => exact ⟨ha, hb⟩, fun ⟨ha, hb⟩ => .or _ _ ha hb⟩
  | .binaryApp _ a b => by
    simp only [parserImageB, Bool.and_eq_true, ← parserImage_iff a, ← parserImage_iff b]
    exact ⟨fun h => by cases h with | binaryApp _ _ _ ha hb => exact ⟨ha, hb⟩,
      fun ⟨ha, hb⟩ => .binaryApp _ _ _ ha hb⟩
  | .unaryApp _ a => by
    simp only [parserImageB, ← parserImage_iff a]
    exact ⟨fun h => by cases h with | unaryApp _ _ ha => exact ha, fun ha => .unaryApp _ _ ha⟩
  | .getAttr a _ => by
    simp only [parserImageB, ← parserImage_iff a]
    exact ⟨fun h => by cases h with | getAttr _ _ ha => exact ha, fun ha => .getAttr _ _ ha⟩
  | .hasAttr a _ => by
    simp only [parserImageB, ← parserImage_iff a]
    exact ⟨fun h => by cases h with | hasAttr _ _ ha => exact ha, fun ha => .hasAttr _ _ ha⟩
  | .extHasAttr a k ks => by
    simp only [parserImageB, Bool.and_eq_true, ← parserImage_iff a]
    exact ⟨fun h => by cases h with | extHasAttr _ _ _ hk ha => exact ⟨hk, ha⟩,
      fun ⟨hk, ha⟩ => .extHasAttr _ _ _ hk ha⟩
  | .set xs => by
    simp only [parserImageB, ← parserImageList_iff xs]
    exact ⟨fun h => by cases h with | set _ hs => exact hs, fun hs => .set _ hs⟩
  | .call _ xs => by
    simp only [parserImageB, ← parserImageList_iff xs]
    exact ⟨fun h => by cases h with | call _ _ hs => exact hs, fun hs => .call _ _ hs⟩
  | .record axs => by
    simp only [parserImageB, Bool.and_eq_true, decide_eq_true_eq, ← parserImageRecord_iff axs]
    exact ⟨fun h => by cases h with | record _ hn hs => exact ⟨hn, hs⟩,
      fun ⟨hn, hs⟩ => .record _ hn hs⟩

theorem parserImageList_iff : ∀ (xs : List Expr), (∀ x ∈ xs, ParserImage x) ↔ parserImageListB xs = true
  | [] => by simp [parserImageListB]
  | x :: xs => by
    simp only [parserImageListB, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp,
      ← parserImage_iff x, ← parserImageList_iff xs]

theorem parserImageRecord_iff : ∀ (axs : List (Attr × Expr)),
    (∀ x ∈ axs.map Prod.snd, ParserImage x) ↔ parserImageRecordB axs = true
  | [] => by simp [parserImageRecordB]
  | (a, x) :: axs => by
    simp only [parserImageRecordB, Bool.and_eq_true, List.map_cons, List.mem_cons, forall_eq_or_imp,
      ← parserImage_iff x, ← parserImageRecord_iff axs]
end

/-- `DeadOperand decl syn env x`, decided. -/
def deadOperandOk (decl syn : Bool) (env : TypeEnv) (x : Expr) : Bool :=
  (!decl || entitiesDeclaredB env.ets env.acts x) && (!syn || parserImageB x)

theorem deadOperand_iff {decl syn : Bool} {env : TypeEnv} {x : Expr} :
    DeadOperand decl syn env x ↔ deadOperandOk decl syn env x = true := by
  simp only [deadOperandOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h
    cases h
    next hd hp =>
    refine ⟨?_, ?_⟩
    · cases hd with
      | yes _ _ _ _ h => exact .inr (entitiesDeclaredB_of x h)
      | no => exact .inl rfl
    · cases hp with
      | yes _ _ h => exact .inr ((parserImage_iff x).mp h)
      | no => exact .inl rfl
  · rintro ⟨hd, hp⟩
    refine .mk _ _ ?_ ?_
    · rcases hd with rfl | h
      · exact .no _ _ _
      · exact .yes _ _ _ _ (entitiesDeclared_of_B x h)
    · rcases hp with rfl | h
      · exact .no _
      · exact .yes _ _ ((parserImage_iff x).mpr h)

end Cedar.Validation.Relational
