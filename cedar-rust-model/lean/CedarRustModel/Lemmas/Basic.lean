module

public import CedarRustModel.Convert
public import CedarRustModel.Ext.Values
public import Cedar.Thm.Data.LT
public import Cedar.Thm.Data.List
public import Cedar.Thm.Data.Control

/-! Basic lemmas: list conversion, cloning, and equality. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model Cedar.Spec Cedar.Data

public section

@[simp] theorem Except.pure_eq_ok' {ε α} (a : α) : (pure a : Except ε α) = .ok a := rfl
@[simp] theorem Except.map_ok' {ε α β} (f : α → β) (a : α) :
    (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl
@[simp] theorem Except.map_error' {ε α β} (f : α → β) (e : ε) :
    (f <$> (Except.error e : Except ε α)) = .error e := rfl

@[simp] theorem List.toList_nil {α} : List.toList (.Nil : value.List α) = [] := rfl
@[simp] theorem List.toList_cons {α} (x : α) (xs : value.List α) :
    List.toList (.Cons x xs) = x :: List.toList xs := rfl

theorem I64.toInt_ofInt_val (i : I64) : (Int64.ofInt i.val).toInt = i.val := by
  have h := i.hBounds
  rw [Int64.toInt_ofInt]
  simp at h ⊢

theorem I64.ofInt_val_inj (i j : I64) : Int64.ofInt i.val = Int64.ofInt j.val ↔ i = j := by
  constructor
  · intro h
    have h' := congrArg Int64.toInt h
    rw [I64.toInt_ofInt_val, I64.toInt_ofInt_val] at h'
    exact IScalar.val_eq_imp _ _ h'
  · intro h; subst h; rfl

@[simp] theorem Str.toSpec_toList (s : value.List Char) : (Str.toSpec s).toList = List.toList s := by
  simp [Str.toSpec]

theorem Str.toSpec_eq_iff (a b : value.List Char) :
    Str.toSpec a = Str.toSpec b ↔ List.toList a = List.toList b := by
  constructor
  · intro h; exact String.ofList_injective h
  · intro h; simp [Str.toSpec, h]

@[simp] theorem Str.toSpec_cons_eq_cons (c d : Char) (a b : value.List Char) :
    Str.toSpec (.Cons c a) = Str.toSpec (.Cons d b) ↔ c = d ∧ Str.toSpec a = Str.toSpec b := by
  simp [Str.toSpec_eq_iff]

@[simp] theorem Str.toSpec_nil_eq_cons (d : Char) (b : value.List Char) :
    ¬ Str.toSpec .Nil = Str.toSpec (.Cons d b) := by
  simp [Str.toSpec_eq_iff]

@[simp] theorem Str.toSpec_cons_eq_nil (d : Char) (b : value.List Char) :
    ¬ Str.toSpec (.Cons d b) = Str.toSpec .Nil := by
  simp [Str.toSpec_eq_iff]

/-! ## Cloning -/

theorem clone_str_ok (s : value.List Char) : value.clone_str s = ok s := by
  induction s with
  | Nil => rw [value.clone_str.eq_def]
  | Cons c s ih => rw [value.clone_str.eq_def]; simp [ih]

theorem clone_strs_ok (s : value.List (value.List Char)) : value.clone_strs s = ok s := by
  induction s with
  | Nil => rw [value.clone_strs.eq_def]
  | Cons c s ih => rw [value.clone_strs.eq_def]; simp [ih, clone_str_ok]

theorem clone_name_ok (n : value.Name) : value.clone_name n = ok n := by
  simp [value.clone_name, clone_str_ok, clone_strs_ok]

theorem clone_uid_ok (u : value.EntityUID) : value.clone_uid u = ok u := by
  simp [value.clone_uid, clone_str_ok, clone_name_ok]

theorem clone_prim_ok (p : value.Prim) : value.clone_prim p = ok p := by
  cases p <;> simp [value.clone_prim, clone_str_ok, clone_uid_ok]

mutual
theorem clone_value_ok : (v : value.Value) → value.clone_value v = ok v
  | .Prim p => by rw [value.clone_value.eq_def]; simp [clone_prim_ok]
  | .Set vs => by rw [value.clone_value.eq_def]; simp [clone_values_ok vs]
  | .Record avs => by rw [value.clone_value.eq_def]; simp [clone_attrs_ok avs]
  | .Ext e => by rw [value.clone_value.eq_def]; simp [clone_ext_ok]
theorem clone_values_ok : (vs : value.List value.Value) → value.clone_values vs = ok vs
  | .Nil => by rw [value.clone_values.eq_def]
  | .Cons v vs => by
    rw [value.clone_values.eq_def]; simp [clone_value_ok v, clone_values_ok vs]
theorem clone_attrs_ok :
    (vs : value.List (value.List Char × value.Value)) → value.clone_attrs vs = ok vs
  | .Nil => by rw [value.clone_attrs.eq_def]
  | .Cons (a, v) vs => by
    rw [value.clone_attrs.eq_def]; simp [clone_str_ok, clone_value_ok v, clone_attrs_ok vs]
end

/-! ## Equality -/

theorem str_eq_ok (a b : value.List Char) :
    value.str_eq a b = ok (decide (Str.toSpec a = Str.toSpec b)) := by
  induction a generalizing b with
  | Nil => cases b <;> rw [value.str_eq.eq_def] <;> simp
  | Cons c a ih =>
    cases b with
    | Nil => rw [value.str_eq.eq_def]; simp
    | Cons d b =>
      rw [value.str_eq.eq_def]; simp only
      by_cases h : c = d <;> simp [h, ih]

theorem strs_eq_ok (a b : value.List (value.List Char)) :
    value.strs_eq a b =
      ok (decide ((List.toList a).map Str.toSpec = (List.toList b).map Str.toSpec)) := by
  induction a generalizing b with
  | Nil => cases b <;> rw [value.strs_eq.eq_def] <;> simp
  | Cons c a ih =>
    cases b with
    | Nil => rw [value.strs_eq.eq_def]; simp
    | Cons d b =>
      rw [value.strs_eq.eq_def]; simp only [str_eq_ok]
      by_cases h : Str.toSpec c = Str.toSpec d <;> simp [h, ih]

theorem name_eq_ok (a b : value.Name) :
    value.name_eq a b = ok (decide (Name.toSpec a = Name.toSpec b)) := by
  simp only [value.name_eq, str_eq_ok, Name.toSpec, Name.mk.injEq]
  by_cases h : Str.toSpec a.id = Str.toSpec b.id <;> simp [h, strs_eq_ok]

theorem uid_eq_ok (a b : value.EntityUID) :
    value.uid_eq a b = ok (decide (EntityUID.toSpec a = EntityUID.toSpec b)) := by
  simp only [value.uid_eq, name_eq_ok, EntityUID.toSpec, EntityUID.mk.injEq]
  by_cases h : Name.toSpec a.ty = Name.toSpec b.ty <;> simp [h, str_eq_ok]

theorem prim_eq_ok (a b : value.Prim) :
    value.prim_eq a b = ok (decide (Prim.toSpec a = Prim.toSpec b)) := by
  cases a <;> cases b <;> simp [value.prim_eq, Prim.toSpec, str_eq_ok, uid_eq_ok, I64.ofInt_val_inj]

mutual
theorem value_eq_ok : (a b : value.Value) →
    value.value_eq a b = ok (decide (Value.toSpec a = Value.toSpec b))
  | .Prim x, .Prim y => by rw [value.value_eq.eq_def]; simp [prim_eq_ok, Value.toSpec]
  | .Prim x, .Set y => by rw [value.value_eq.eq_def]; simp [Value.toSpec]
  | .Prim x, .Record y => by rw [value.value_eq.eq_def]; simp [Value.toSpec]
  | .Set x, .Prim y => by rw [value.value_eq.eq_def]; simp [Value.toSpec]
  | .Set x, .Set y => by rw [value.value_eq.eq_def]; simp [values_eq_ok x y, Value.toSpec]
  | .Set x, .Record y => by rw [value.value_eq.eq_def]; simp [Value.toSpec]
  | .Record x, .Prim y => by rw [value.value_eq.eq_def]; simp [Value.toSpec]
  | .Record x, .Set y => by rw [value.value_eq.eq_def]; simp [Value.toSpec]
  | .Record x, .Record y => by rw [value.value_eq.eq_def]; simp [attrs_eq_ok x y, Value.toSpec]
  | .Prim x, .Ext y => by rw [value.value_eq.eq_def]; simp [Value.toSpec]
  | .Set x, .Ext y => by rw [value.value_eq.eq_def]; simp [Value.toSpec]
  | .Record x, .Ext y => by rw [value.value_eq.eq_def]; simp [Value.toSpec]
  | .Ext x, .Prim y => by rw [value.value_eq.eq_def]; simp [Value.toSpec]
  | .Ext x, .Set y => by rw [value.value_eq.eq_def]; simp [Value.toSpec]
  | .Ext x, .Record y => by rw [value.value_eq.eq_def]; simp [Value.toSpec]
  | .Ext x, .Ext y => by rw [value.value_eq.eq_def]; simp [ext_eq_ok x y, Value.toSpec]
theorem values_eq_ok : (a b : value.List value.Value) →
    value.values_eq a b = ok (decide (Values.toSpec a = Values.toSpec b))
  | .Nil, .Nil => by rw [value.values_eq.eq_def]; simp [Values.toSpec]
  | .Nil, .Cons _ _ => by rw [value.values_eq.eq_def]; simp [Values.toSpec]
  | .Cons _ _, .Nil => by rw [value.values_eq.eq_def]; simp [Values.toSpec]
  | .Cons x a, .Cons y b => by
    rw [value.values_eq.eq_def]
    simp only [value_eq_ok x y, Values.toSpec, _root_.List.cons.injEq]
    by_cases h : Value.toSpec x = Value.toSpec y <;> simp [h, values_eq_ok a b]
theorem attrs_eq_ok : (a b : value.List (value.List Char × value.Value)) →
    value.attrs_eq a b = ok (decide (Attrs.toSpec a = Attrs.toSpec b))
  | .Nil, .Nil => by rw [value.attrs_eq.eq_def]; simp [Attrs.toSpec]
  | .Nil, .Cons _ _ => by rw [value.attrs_eq.eq_def]; simp [Attrs.toSpec]
  | .Cons _ _, .Nil => by rw [value.attrs_eq.eq_def]; simp [Attrs.toSpec]
  | .Cons (k, x) a, .Cons (l, y) b => by
    rw [value.attrs_eq.eq_def]
    simp only [str_eq_ok, Attrs.toSpec, _root_.List.cons.injEq, Prod.mk.injEq]
    by_cases h : Str.toSpec k = Str.toSpec l <;>
    by_cases h' : Value.toSpec x = Value.toSpec y <;>
    simp [h, h', value_eq_ok x y, attrs_eq_ok a b]
end

end -- public section

end CedarRustModel
