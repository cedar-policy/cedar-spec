module

public import CedarRustModel.Lemmas.Canonical
public import CedarRustModel.Lemmas.Lookup
public import CedarRustModel.Lemmas.Wildcard
public import Cedar.Thm.Data.Set
import all Cedar.Data.Set
import all Cedar.Data.Map
import all Cedar.Data.Int64
import all Aeneas.Std.Scalar.CheckedOps.Add
import all Aeneas.Std.Scalar.CheckedOps.Sub
import all Aeneas.Std.Scalar.CheckedOps.Mul

/-! Operators and attribute access. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model Cedar.Spec Cedar.Data

public section

@[simp] theorem Result.toSpec_Ok {α β} (f : α → β) (v : α) :
    Result.toSpec f (.Ok v) = .ok (f v) := rfl
@[simp] theorem Result.toSpec_Err {α β} (f : α → β) (e : value.Error) :
    Result.toSpec f (.Err e : core.result.Result α value.Error) = .error (Error.toSpec e) := rfl

@[simp] theorem Value.toSpec_prim (p : value.Prim) : Value.toSpec (.Prim p) = .prim (Prim.toSpec p) := by
  simp [Value.toSpec]
@[simp] theorem Value.toSpec_set (vs : value.List value.Value) :
    Value.toSpec (.Set vs) = .set (Set.mk (Values.toSpec vs)) := by
  simp [Value.toSpec]
@[simp] theorem Value.toSpec_record (avs : value.List (value.List Char × value.Value)) :
    Value.toSpec (.Record avs) = .record (Map.mk (Attrs.toSpec avs)) := by
  simp [Value.toSpec]
@[simp] theorem Prim.toSpec_bool (b : Bool) : Prim.toSpec (.Bool b) = .bool b := rfl
@[simp] theorem Prim.toSpec_int (i : I64) : Prim.toSpec (.Int i) = .int (Int64.ofInt i.val) := rfl
@[simp] theorem Prim.toSpec_string (s : value.List Char) :
    Prim.toSpec (.String s) = .string (Str.toSpec s) := rfl
@[simp] theorem Prim.toSpec_entityUID (u : value.EntityUID) :
    Prim.toSpec (.EntityUID u) = .entityUID (EntityUID.toSpec u) := rfl

@[simp] theorem Values.toSpec_nil : Values.toSpec .Nil = [] := by simp [Values.toSpec]
@[simp] theorem Values.toSpec_cons (v : value.Value) (vs : value.List value.Value) :
    Values.toSpec (.Cons v vs) = Value.toSpec v :: Values.toSpec vs := by simp [Values.toSpec]
@[simp] theorem Attrs.toSpec_nil : Attrs.toSpec .Nil = [] := by simp [Attrs.toSpec]
@[simp] theorem Attrs.toSpec_cons (a : value.List Char) (v : value.Value)
    (avs : value.List (value.List Char × value.Value)) :
    Attrs.toSpec (.Cons (a, v) avs) = (Str.toSpec a, Value.toSpec v) :: Attrs.toSpec avs := by
  simp [Attrs.toSpec]

/-! ## Integers -/

theorem int_or_err_ok (o : Option I64) (n : Int)
    (h : match o with
      | some z => z.val = n
      | none => ¬ (Int64.MIN ≤ n ∧ n ≤ Int64.MAX)) :
    ∃ r, evaluator.int_or_err o = ok r ∧
      Result.toSpec Value.toSpec r = intOrErr (Int64.ofInt? n) := by
  cases o with
  | none =>
    simp only at h
    have : Int64.ofInt? n = none := by simp [Int64.ofInt?, h]
    simp [evaluator.int_or_err, this, intOrErr, Error.toSpec]
  | some z =>
    simp only at h
    have hb := z.hBounds
    have : Int64.ofInt? n = some (Int64.ofInt z.val) := by
      rw [← h]
      apply Int64.ofInt?_some_iff.mp
      simp [Int64.MIN, Int64.MAX] at hb ⊢
      omega
    simp [evaluator.int_or_err, this, intOrErr, Prim.toSpec]

theorem checked_add_ok (i j : I64) :
    ∃ r, evaluator.int_or_err (I64.checked_add i j) = ok r ∧
      Result.toSpec Value.toSpec r =
        intOrErr ((Int64.ofInt i.val).add? (Int64.ofInt j.val)) := by
  simp only [Int64.add?, I64.toInt_ofInt_val]
  apply int_or_err_ok
  have := I64.checked_add_bv_spec i j
  simp only [I64.checked_add]
  split at this <;> rename_i heq <;> rw [heq]
  · exact this.2.2.1
  · simp [Int64.MIN, Int64.MAX, I64.min_eq, I64.max_eq] at this ⊢; omega

theorem checked_sub_ok (i j : I64) :
    ∃ r, evaluator.int_or_err (I64.checked_sub i j) = ok r ∧
      Result.toSpec Value.toSpec r =
        intOrErr ((Int64.ofInt i.val).sub? (Int64.ofInt j.val)) := by
  simp only [Int64.sub?, I64.toInt_ofInt_val]
  apply int_or_err_ok
  have := I64.checked_sub_bv_spec i j
  simp only [I64.checked_sub]
  split at this <;> rename_i heq <;> rw [heq]
  · exact this.2.2.1
  · simp [Int64.MIN, Int64.MAX, I64.min_eq, I64.max_eq] at this ⊢; omega

theorem checked_mul_ok (i j : I64) :
    ∃ r, evaluator.int_or_err (I64.checked_mul i j) = ok r ∧
      Result.toSpec Value.toSpec r =
        intOrErr ((Int64.ofInt i.val).mul? (Int64.ofInt j.val)) := by
  simp only [Int64.mul?, I64.toInt_ofInt_val]
  apply int_or_err_ok
  have := I64.checked_mul_bv_spec i j
  simp only [I64.checked_mul]
  split at this <;> rename_i heq <;> rw [heq]
  · exact this.2.2.1
  · simp [Int64.MIN, Int64.MAX, I64.min_eq, I64.max_eq] at this ⊢; omega

theorem checked_neg_ok (i : I64) :
    ∃ r, evaluator.int_or_err (I64.checked_sub 0#i64 i) = ok r ∧
      Result.toSpec Value.toSpec r = intOrErr (Int64.ofInt i.val).neg? := by
  simp only [Int64.neg?, I64.toInt_ofInt_val]
  apply int_or_err_ok
  have := I64.checked_sub_bv_spec 0#i64 i
  simp only [I64.checked_sub]
  split at this <;> rename_i heq <;> rw [heq]
  · simpa using this.2.2.1
  · simp [Int64.MIN, Int64.MAX, I64.min_eq, I64.max_eq] at this ⊢; omega


/-! ## Unary operators -/

theorem apply1_ok (op : expr.UnaryOp) (v : value.Value) :
    ∃ r, evaluator.apply1 op v = ok r ∧
      Result.toSpec Value.toSpec r = apply₁ (UnaryOp.toSpec op) (Value.toSpec v) := by
  cases op <;> cases v <;> try (rename_i p; cases p)
  all_goals simp [evaluator.apply1, UnaryOp.toSpec, apply₁, Error.toSpec, evaluator.bool_val,
    lift, Set.isEmpty, Set.empty, wildcard_match_ok, wildcardMatch_eq_wm, Str.toSpec,
    name_eq_ok, EntityUID.toSpec, Value.toSpec, Ext.toSpec]
  case Neg.Prim.Int i => exact checked_neg_ok i
  case Is.Prim.EntityUID => rfl

/-! ## Entity membership and tags -/

theorem in_e_ok (u₁ u₂ : value.EntityUID) (es : value.List (value.EntityUID × entities.EntityData)) :
    evaluator.in_e u₁ u₂ es =
      ok (inₑ (EntityUID.toSpec u₁) (EntityUID.toSpec u₂) (Entities.toSpec es)) := by
  obtain ⟨o, h₁, h₂⟩ := entities_find_ok es u₁
  simp only [evaluator.in_e, uid_eq_ok, inₑ, Entities.ancestorsOrEmpty, ← h₂, h₁]
  by_cases h : EntityUID.toSpec u₁ = EntityUID.toSpec u₂
  · simp [h]
  · cases o <;> simp [h, uids_contains_ok, EntityData.toSpec, Set.empty, Set.contains, Set.elts]

theorem inₛ_mk (uid : Cedar.Spec.EntityUID) (l : _root_.List Cedar.Spec.Value) (es : Entities) :
    inₛ uid (Set.mk l) es =
      (match l.mapM Value.asEntityUID with
       | .ok uids => .ok (Value.prim (.bool (uids.any (inₑ uid · es))))
       | .error _ => .error .typeError) := by
  unfold inₛ Set.mapOrErr
  simp only [Set.elts]
  cases l.mapM Value.asEntityUID <;> simp [Set.any_make]

theorem in_s_ok (u : value.EntityUID) (vs : value.List value.Value)
    (es : value.List (value.EntityUID × entities.EntityData)) :
    ∃ r, evaluator.in_s u vs es = ok r ∧
      Result.toSpec (fun b => Value.prim (.bool b)) r =
        inₛ (EntityUID.toSpec u) (Set.mk (Values.toSpec vs)) (Entities.toSpec es) := by
  rw [inₛ_mk]
  induction vs with
  | Nil => rw [evaluator.in_s.eq_def]; simp
  | Cons v rest ih =>
    rw [evaluator.in_s.eq_def]
    cases v with
    | Prim p =>
      cases p <;> simp [Value.asEntityUID, Error.toSpec]
      rename_i u₂
      obtain ⟨r, h₁, h₂⟩ := ih
      simp only [in_e_ok, h₁]
      revert h₂
      cases (Values.toSpec rest).mapM Value.asEntityUID <;> cases r <;>
        simp [Error.toSpec] <;> intros <;> simp_all <;> split <;> simp_all
    | Set _ => simp [Value.asEntityUID, Error.toSpec]
    | Record _ => simp [Value.asEntityUID, Error.toSpec]
    | Ext _ => simp [Value.asEntityUID, Error.toSpec, Value.toSpec]

theorem has_tag_ok (u : value.EntityUID) (t : value.List Char)
    (es : value.List (value.EntityUID × entities.EntityData)) :
    evaluator.has_tag u t es =
      ok ((Entities.tagsOrEmpty (Entities.toSpec es) (EntityUID.toSpec u)).contains (Str.toSpec t)) := by
  obtain ⟨o, h₁, h₂⟩ := entities_find_ok es u
  simp only [evaluator.has_tag, h₁, Entities.tagsOrEmpty, ← h₂]
  cases o <;> simp [attrs_contains_ok, EntityData.toSpec, Map.empty, Map.contains, Map.find?,
    Map.toList]

theorem get_tag_ok (u : value.EntityUID) (t : value.List Char)
    (es : value.List (value.EntityUID × entities.EntityData)) :
    ∃ r, evaluator.get_tag u t es = ok r ∧
      Result.toSpec Value.toSpec r = getTag (EntityUID.toSpec u) (Str.toSpec t) (Entities.toSpec es) := by
  obtain ⟨o, h₁, h₂⟩ := entities_find_ok es u
  simp only [evaluator.get_tag, h₁, getTag, Entities.tags, Map.findOrErr, ← h₂]
  cases o with
  | none => simp [Error.toSpec]
  | some d =>
    obtain ⟨o', h₃, h₄⟩ := attrs_find_ok d.tags t
    simp only [h₃, Option.map_some, EntityData.toSpec, ← h₄]
    cases o' <;> simp [h₃, ← h₄, Error.toSpec, clone_value_ok]

/-! ## Binary operators -/

theorem apply2_ok (op : expr.BinaryOp) (v₁ v₂ : value.Value)
    (es : value.List (value.EntityUID × entities.EntityData)) :
    ∃ r, evaluator.apply2 op v₁ v₂ es = ok r ∧
      Result.toSpec Value.toSpec r =
        apply₂ (BinaryOp.toSpec op) (Value.toSpec v₁) (Value.toSpec v₂) (Entities.toSpec es) := by
  cases op
  case Less | LessEq =>
    rcases v₁ with ((_|_|_|_)|_|_|(_|_|_|_)) <;> rcases v₂ with ((_|_|_|_)|_|_|(_|_|_|_)) <;>
    simp [evaluator.apply2, BinaryOp.toSpec, apply₂, Error.toSpec, evaluator.bool_val, lift,
      Value.toSpec, Ext.toSpec, XV.dt_lt_iff, XV.dt_le_iff, XV.dur_lt_iff, XV.dur_le_iff,
      Int64.lt_iff_toInt_lt, Int64.le_iff_toInt_le, I64.toInt_ofInt_val]
  all_goals rcases v₁ with ((_|_|_|_)|_|_|_) <;> rcases v₂ with ((_|_|_|_)|_|_|_) <;>
    simp [evaluator.apply2, BinaryOp.toSpec, apply₂, Error.toSpec, evaluator.bool_val, lift,
      value_eq_ok, in_e_ok, has_tag_ok, hasTag, values_contains_ok', values_sub_ok,
      values_intersect_ok, Value.toSpec, Ext.toSpec, XV.dt_lt_iff, XV.dt_le_iff, XV.dur_lt_iff,
      XV.dur_le_iff, XV.val_lt', XV.val_le']
  case Mem.Prim.EntityUID.Set u vs =>
    obtain ⟨r, h₁, h₂⟩ := in_s_ok u vs es
    rw [← h₂]
    cases r <;> simp [h₁, evaluator.bool_val]
  case GetTag.Prim.EntityUID.Prim.String u t => exact get_tag_ok u t es
  case Add.Prim.Int.Prim.Int i j => exact checked_add_ok i j
  case Sub.Prim.Int.Prim.Int i j => exact checked_sub_ok i j
  case Mul.Prim.Int.Prim.Int i j => exact checked_mul_ok i j
  all_goals (rw [Bool.eq_iff_iff]; simp)

/-! ## Attributes -/

theorem has_attr_ok (v : value.Value) (a : value.List Char)
    (es : value.List (value.EntityUID × entities.EntityData)) :
    ∃ r, evaluator.has_attr v a es = ok r ∧
      Result.toSpec Value.toSpec r = hasAttr (Value.toSpec v) (Str.toSpec a) (Entities.toSpec es) := by
  rcases v with ((_|_|_|u)|_|avs|_) <;>
    simp [evaluator.has_attr, hasAttr, attrsOf, Error.toSpec, evaluator.bool_val, attrs_contains_ok, Value.toSpec]
  case Prim.EntityUID =>
    obtain ⟨o, h₁, h₂⟩ := entities_find_ok es u
    simp only [evaluator.entity_has_attr, h₁, Entities.attrsOrEmpty, ← h₂]
    cases o <;> simp [attrs_contains_ok, EntityData.toSpec, Map.empty, Map.contains, Map.find?,
      Map.toList]

theorem get_attr_ok (v : value.Value) (a : value.List Char)
    (es : value.List (value.EntityUID × entities.EntityData)) :
    ∃ r, evaluator.get_attr v a es = ok r ∧
      Result.toSpec Value.toSpec r = getAttr (Value.toSpec v) (Str.toSpec a) (Entities.toSpec es) := by
  have hfind : ∀ avs : value.List (value.List Char × value.Value),
      ∃ r, evaluator.attrs_find_or_err avs a = ok r ∧
        Result.toSpec Value.toSpec r =
          (Map.mk (Attrs.toSpec avs)).findOrErr (Str.toSpec a) Error.attrDoesNotExist := by
    intro avs
    obtain ⟨o, h₁, h₂⟩ := attrs_find_ok avs a
    simp only [evaluator.attrs_find_or_err, h₁, Map.findOrErr, ← h₂]
    cases o <;> simp [Error.toSpec, clone_value_ok]
  rcases v with ((_|_|_|u)|_|avs|_) <;>
    simp [evaluator.get_attr, getAttr, attrsOf, Error.toSpec, Value.toSpec]
  case Record => exact hfind avs
  case Prim.EntityUID =>
    obtain ⟨o, h₁, h₂⟩ := entities_find_ok es u
    simp only [evaluator.entity_attr_or_err, h₁, Entities.attrs, Map.findOrErr, ← h₂]
    cases o with
    | none => simp [Error.toSpec]
    | some d => simpa [EntityData.toSpec, Map.findOrErr] using hfind d.attrs

theorem has_attrs_ok (attrs : value.List (value.List Char)) :
    ∀ (v : value.Value) (es : value.List (value.EntityUID × entities.EntityData)),
    ∃ r, evaluator.has_attrs v attrs es = ok r ∧
      Result.toSpec Value.toSpec r =
        hasAttrs.loop (Value.toSpec v) ((List.toList attrs).map Str.toSpec) (Entities.toSpec es) := by
  induction attrs with
  | Nil => intro v es; rw [evaluator.has_attrs.eq_def]; simp [hasAttrs.loop, evaluator.bool_val]
  | Cons a rest ih =>
    intro v es
    have hrec : ∀ avs : value.List (value.List Char × value.Value),
        ∃ r, evaluator.attrs_has_attrs avs a rest es = ok r ∧
          Result.toSpec Value.toSpec r =
            (match (Map.mk (Attrs.toSpec avs)).find? (Str.toSpec a) with
             | some v₁ => hasAttrs.loop v₁ ((List.toList rest).map Str.toSpec) (Entities.toSpec es)
             | none => .ok (Value.prim (.bool false))) := by
      intro avs
      obtain ⟨o, h₁, h₂⟩ := attrs_find_ok avs a
      rw [evaluator.attrs_has_attrs.eq_def]
      simp only [h₁, ← h₂]
      cases o with
      | none => simp [evaluator.bool_val]
      | some v₁ => simpa using ih v₁ es
    rw [evaluator.has_attrs.eq_def]
    rcases v with ((_|_|_|u)|_|avs|_) <;>
      simp [hasAttrs.loop, attrsOf, Error.toSpec, Value.toSpec]
    case Record => exact hrec avs
    case Prim.EntityUID =>
      obtain ⟨o, h₁, h₂⟩ := entities_find_ok es u
      rw [evaluator.entity_has_attrs.eq_def]
      simp only [h₁, Entities.attrsOrEmpty, ← h₂]
      cases o with
      | none => simp [evaluator.bool_val, Map.empty, Map.find?, Map.toList]
      | some d =>
        obtain ⟨r, hr₁, hr₂⟩ := hrec d.attrs
        refine ⟨r, by simp [hr₁], ?_⟩
        rw [hr₂]; simp only [Option.map_some]; rfl

theorem as_bool_ok (r : core.result.Result value.Value value.Error) :
    ∃ r', evaluator.as_bool r = ok r' ∧
      Result.toSpec id r' = (Result.toSpec Value.toSpec r).as Bool := by
  rcases r with (((_|_|_|_)|_|_|_)|_) <;>
    simp [evaluator.as_bool, Result.as, Value.asBool, Error.toSpec, Coe.coe, Value.toSpec]

end -- public section

end CedarRustModel
