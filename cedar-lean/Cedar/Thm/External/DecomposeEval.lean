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
import Cedar.Thm.Data
import Cedar.Thm.Authorization.Authorizer

/-!
Evaluation is insensitive to entities it cannot reach.

Fix a predicate `safe` on entity UIDs and two entity stores `es₁`, `es₂` that
agree on every safe UID. If the request's principal, action, resource, and
context mention only safe UIDs, every attribute and tag value in `es₁` mentions
only safe UIDs, and an expression's literals are all safe, then evaluating the
expression gives the same result on both stores, and any value it produces
mentions only safe UIDs.

This file is independent of schemas. `Cedar.Thm.External.Decompose` instantiates
`safe` with "not a declared action, or in the request action's closure".
-/

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

/-- `v` mentions only UIDs satisfying `safe`. -/
inductive Value.Safe (safe : EntityUID → Prop) : Value → Prop where
  | bool (b : Bool) : Value.Safe safe (.prim (.bool b))
  | int (i : Int64) : Value.Safe safe (.prim (.int i))
  | string (s : String) : Value.Safe safe (.prim (.string s))
  | uid (u : EntityUID) (h : safe u) : Value.Safe safe (.prim (.entityUID u))
  | set (s : Set Value) (h : ∀ v ∈ s, Value.Safe safe v) : Value.Safe safe (.set s)
  | record (m : Map Attr Value) (h : ∀ k v, m.find? k = some v → Value.Safe safe v) :
      Value.Safe safe (.record m)
  | ext (x : Ext) : Value.Safe safe (.ext x)

/-- The entity data in `es` only holds attribute and tag values that mention
    safe UIDs. Ancestors are not constrained: the evaluator only tests them for
    membership and never returns them as values. -/
def StoreSafe (safe : EntityUID → Prop) (es : Entities) : Prop :=
  ∀ u d, es.find? u = some d →
    (∀ k v, d.attrs.find? k = some v → Value.Safe safe v) ∧
    (∀ k v, d.tags.find? k = some v → Value.Safe safe v)

/-- The request mentions only safe UIDs. -/
def RequestSafe (safe : EntityUID → Prop) (req : Request) : Prop :=
  safe req.principal ∧ safe req.action ∧ safe req.resource ∧
  Value.Safe safe (.record req.context)

section

variable {safe : EntityUID → Prop} {req : Request} {es₁ es₂ : Entities}

----- Store reads agree on safe UIDs -----

theorem ancestorsOrEmpty_agree {u : EntityUID}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hu : safe u) :
    es₁.ancestorsOrEmpty u = es₂.ancestorsOrEmpty u := by
  simp only [Entities.ancestorsOrEmpty, hagree u hu]

theorem attrsOrEmpty_agree {u : EntityUID}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hu : safe u) :
    es₁.attrsOrEmpty u = es₂.attrsOrEmpty u := by
  simp only [Entities.attrsOrEmpty, hagree u hu]

theorem attrs_agree {u : EntityUID}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hu : safe u) :
    es₁.attrs u = es₂.attrs u := by
  simp only [Entities.attrs, Map.findOrErr, hagree u hu]

theorem tagsOrEmpty_agree {u : EntityUID}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hu : safe u) :
    es₁.tagsOrEmpty u = es₂.tagsOrEmpty u := by
  simp only [Entities.tagsOrEmpty, hagree u hu]

theorem tags_agree {u : EntityUID}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hu : safe u) :
    es₁.tags u = es₂.tags u := by
  simp only [Entities.tags, Map.findOrErr, hagree u hu]

----- Operators agree when their first operand is safe -----

theorem apply₂_agree {op : BinaryOp} {v₁ v₂ : Value}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hv₁ : Value.Safe safe v₁) :
    apply₂ op v₁ v₂ es₁ = apply₂ op v₁ v₂ es₂ := by
  cases hv₁ with
  | uid u hu =>
    unfold apply₂
    split <;> try rfl
    all_goals
      rename_i heq
      simp only [Value.prim.injEq, Prim.entityUID.injEq] at heq
      subst heq
    · simp only [inₑ, ancestorsOrEmpty_agree hagree hu]
    · simp only [inₛ, inₑ, ancestorsOrEmpty_agree hagree hu]
    · simp only [hasTag, tagsOrEmpty_agree hagree hu]
    · simp only [getTag, tags_agree hagree hu]
  | _ =>
    unfold apply₂
    split <;> first | rfl | (rename_i heq; simp at heq)

theorem attrsOf_agree {v : Value}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hv : Value.Safe safe v) :
    attrsOf v es₁.attrs = attrsOf v es₂.attrs ∧
    attrsOf v (fun uid => .ok (es₁.attrsOrEmpty uid)) =
      attrsOf v (fun uid => .ok (es₂.attrsOrEmpty uid)) := by
  cases hv with
  | uid u hu => simp only [attrsOf, attrs_agree hagree hu, attrsOrEmpty_agree hagree hu, and_self]
  | _ => simp only [attrsOf, and_self]

theorem hasAttr_agree {v : Value} {a : Attr}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hv : Value.Safe safe v) :
    hasAttr v a es₁ = hasAttr v a es₂ := by
  simp only [hasAttr, (attrsOf_agree hagree hv).2]

theorem getAttr_agree {v : Value} {a : Attr}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hv : Value.Safe safe v) :
    getAttr v a es₁ = getAttr v a es₂ := by
  simp only [getAttr, (attrsOf_agree hagree hv).1]

----- Values read from a safe store are safe -----

theorem attrsOf_attrs_safe {v : Value} {r : Map Attr Value}
    (hstore : StoreSafe safe es₁) (hv : Value.Safe safe v)
    (h : attrsOf v es₁.attrs = .ok r) :
    ∀ k v', r.find? k = some v' → Value.Safe safe v' := by
  cases hv with
  | record m hm =>
    simp only [attrsOf, Except.ok.injEq] at h
    subst h
    exact hm
  | uid u _ =>
    simp only [attrsOf, Entities.attrs, Map.findOrErr] at h
    split at h
    · rename_i d hd
      simp only [bind, Except.bind, Except.ok.injEq] at h
      subst h
      exact (hstore u d hd).1
    · simp [bind, Except.bind] at h
  | _ => simp [attrsOf] at h

theorem attrsOf_attrsOrEmpty_safe {v : Value} {r : Map Attr Value}
    (hstore : StoreSafe safe es₁) (hv : Value.Safe safe v)
    (h : attrsOf v (fun uid => .ok (es₁.attrsOrEmpty uid)) = .ok r) :
    ∀ k v', r.find? k = some v' → Value.Safe safe v' := by
  cases hv with
  | record m hm =>
    simp only [attrsOf, Except.ok.injEq] at h
    subst h
    exact hm
  | uid u _ =>
    simp only [attrsOf, Entities.attrsOrEmpty, Except.ok.injEq] at h
    split at h
    · rename_i d hd
      subst h
      exact (hstore u d hd).1
    · subst h
      intro k v' hk
      simp at hk
  | _ => simp [attrsOf] at h

theorem hasAttrs_loop_agree {v : Value} {attrs : List Attr}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hstore : StoreSafe safe es₁)
    (hv : Value.Safe safe v) :
    hasAttrs.loop v attrs es₁ = hasAttrs.loop v attrs es₂ := by
  induction attrs generalizing v with
  | nil => simp only [hasAttrs.loop]
  | cons a rest ih =>
    simp only [hasAttrs.loop, ← (attrsOf_agree hagree hv).2]
    split
    · rename_i r hr
      split
      · rename_i v₁ hv₁
        exact ih (attrsOf_attrsOrEmpty_safe hstore hv hr a v₁ hv₁)
      · rfl
    · rfl

theorem hasAttrs_agree {v : Value} {a : Attr} {rest : List Attr}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hstore : StoreSafe safe es₁)
    (hv : Value.Safe safe v) :
    hasAttrs v a rest es₁ = hasAttrs v a rest es₂ := by
  simp only [hasAttrs, hasAttrs_loop_agree hagree hstore hv]

----- Operator results are safe -----

theorem intOrErr_safe {o : Option Int64} {v : Value} (h : intOrErr o = .ok v) :
    Value.Safe safe v := by
  simp only [intOrErr] at h
  split at h <;> try simp only [Except.ok.injEq, reduceCtorEq] at h
  subst h; exact .int _

theorem apply₁_safe {op : UnaryOp} {v v' : Value} (h : apply₁ op v = .ok v') :
    Value.Safe safe v' := by
  unfold apply₁ at h
  split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h; subst h; exact .bool _)
    | exact intOrErr_safe h
    | simp at h

theorem apply₂_safe {op : BinaryOp} {v₁ v₂ v : Value}
    (hstore : StoreSafe safe es₁) (h : apply₂ op v₁ v₂ es₁ = .ok v) :
    Value.Safe safe v := by
  unfold apply₂ at h
  split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h; subst h; exact .bool _)
    | exact intOrErr_safe h
    | skip
  · -- inₛ
    simp only [inₛ, bind, Except.bind] at h
    split at h <;> try simp only [Except.ok.injEq, reduceCtorEq] at h
    subst h; exact .bool _
  · -- hasTag
    simp only [hasTag, Except.ok.injEq] at h
    subst h; exact .bool _
  · -- getTag
    rename_i uid₁ tag
    simp only [getTag, Entities.tags, Map.findOrErr, bind, Except.bind] at h
    cases hd : es₁.find? uid₁ with
    | none => simp [hd] at h
    | some d =>
      simp only [hd] at h
      cases hv' : d.tags.find? tag with
      | none => simp [hv'] at h
      | some v' =>
        simp only [hv', Except.ok.injEq] at h
        subst h
        exact (hstore uid₁ d hd).2 tag v' hv'
  · simp at h

theorem hasAttr_safe {v v' : Value} {a : Attr} (h : hasAttr v a es₁ = .ok v') :
    Value.Safe safe v' := by
  simp only [hasAttr, bind, Except.bind] at h
  split at h <;> try simp only [Except.ok.injEq, reduceCtorEq] at h
  subst h; exact .bool _

theorem hasAttrs_loop_safe {v v' : Value} {attrs : List Attr}
    (h : hasAttrs.loop v attrs es₁ = .ok v') : Value.Safe safe v' := by
  induction attrs generalizing v with
  | nil =>
    simp only [hasAttrs.loop, Except.ok.injEq] at h
    subst h; exact .bool _
  | cons a rest ih =>
    simp only [hasAttrs.loop] at h
    split at h
    · split at h
      · exact ih h
      · simp only [Except.ok.injEq] at h; subst h; exact .bool _
    · simp at h

theorem hasAttrs_safe {v v' : Value} {a : Attr} {rest : List Attr}
    (h : hasAttrs v a rest es₁ = .ok v') : Value.Safe safe v' := by
  simp only [hasAttrs] at h
  exact hasAttrs_loop_safe h

theorem getAttr_safe {v v' : Value} {a : Attr}
    (hstore : StoreSafe safe es₁) (hv : Value.Safe safe v) (h : getAttr v a es₁ = .ok v') :
    Value.Safe safe v' := by
  simp only [getAttr, bind, Except.bind] at h
  split at h <;> try simp only [reduceCtorEq] at h
  rename_i r hr
  rw [Map.findOrErr_ok_iff_find?_some] at h
  exact attrsOf_attrs_safe hstore hv hr a v' h

theorem call_safe {xfn : ExtFun} {vs : List Value} {v : Value} (h : call xfn vs = .ok v) :
    Value.Safe safe v := by
  unfold call at h
  split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h; subst h; first | exact .bool _ | exact .int _ | exact .ext _)
    | (simp only [res] at h
       split at h
       · simp only [Except.ok.injEq] at h; subst h; exact .ext _
       · simp at h)
    | (simp at h; done)
    | -- A function that decodes its arguments in a `do` block before
      -- returning, such as the variadic `isInRange`, returns a boolean.
      (simp only [bind, Except.bind] at h
       repeat' split at h
       all_goals first
         | (simp only [Except.ok.injEq] at h; subst h; exact .bool _)
         | (simp at h; done))

----- Literals of subexpressions -----

theorem forall_mem_union {P : EntityUID → Prop} {a b : Set EntityUID}
    (h : ∀ u ∈ a ∪ b, P u) : (∀ u ∈ a, P u) ∧ (∀ u ∈ b, P u) :=
  ⟨fun u hu => h u ((Set.mem_union a b u).mpr (.inl hu)),
   fun u hu => h u ((Set.mem_union a b u).mpr (.inr hu))⟩

theorem literalUIDs_set_mem {xs : List Expr} {x : Expr} {u : EntityUID}
    (hx : x ∈ xs) (hu : u ∈ x.literalUIDs) : u ∈ (Expr.set xs).literalUIDs := by
  simp only [Expr.literalUIDs, List.mapUnion₁_eq_mapUnion Expr.literalUIDs]
  exact List.mem_mem_implies_mem_mapUnion hu hx

theorem literalUIDs_call_mem {xfn : ExtFun} {xs : List Expr} {x : Expr} {u : EntityUID}
    (hx : x ∈ xs) (hu : u ∈ x.literalUIDs) : u ∈ (Expr.call xfn xs).literalUIDs := by
  simp only [Expr.literalUIDs, List.mapUnion₁_eq_mapUnion Expr.literalUIDs]
  exact List.mem_mem_implies_mem_mapUnion hu hx

theorem literalUIDs_record_mem {axs : List (Attr × Expr)} {ax : Attr × Expr} {u : EntityUID}
    (hx : ax ∈ axs) (hu : u ∈ ax.snd.literalUIDs) : u ∈ (Expr.record axs).literalUIDs := by
  simp only [Expr.literalUIDs, List.mapUnion₂_eq_mapUnion (fun x : Attr × Expr => x.snd.literalUIDs)]
  exact List.mem_mem_implies_mem_mapUnion (f := fun x : Attr × Expr => x.snd.literalUIDs) hu hx

----- Main lemma -----

/-- Evaluating `x` gives the same result on both stores, and any value it
    produces mentions only safe UIDs. -/
def EvalAgreeSafe (safe : EntityUID → Prop) (x : Expr) (req : Request) (es₁ es₂ : Entities) : Prop :=
  evaluate x req es₁ = evaluate x req es₂ ∧
  ∀ v, evaluate x req es₁ = .ok v → Value.Safe safe v

theorem evaluate_agree_safe (x : Expr)
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u)
    (hstore : StoreSafe safe es₁)
    (hreq : RequestSafe safe req)
    (hlits : ∀ u ∈ x.literalUIDs, safe u) :
    EvalAgreeSafe safe x req es₁ es₂ := by
  unfold EvalAgreeSafe
  cases x with
  | lit p =>
    refine ⟨by simp only [evaluate], ?_⟩
    intro v h
    simp only [evaluate, Except.ok.injEq] at h
    subst h
    cases p with
    | bool b => exact .bool b
    | int i => exact .int i
    | string s => exact .string s
    | entityUID u =>
      apply Value.Safe.uid
      apply hlits u
      simp [Expr.literalUIDs, Set.mem_singleton]
  | var v =>
    refine ⟨by cases v <;> simp only [evaluate], ?_⟩
    intro v' h
    obtain ⟨hp, ha, hr, hc⟩ := hreq
    cases v <;> simp only [evaluate, Except.ok.injEq] at h <;> subst h
    · exact .uid _ hp
    · exact .uid _ ha
    · exact .uid _ hr
    · exact hc
  | ite x₁ x₂ x₃ =>
    simp only [Expr.literalUIDs] at hlits
    have ⟨h₁₂, h₃⟩ := forall_mem_union hlits
    have ⟨h₁, h₂⟩ := forall_mem_union h₁₂
    have ih₁ := evaluate_agree_safe x₁ hagree hstore hreq h₁
    have ih₂ := evaluate_agree_safe x₂ hagree hstore hreq h₂
    have ih₃ := evaluate_agree_safe x₃ hagree hstore hreq h₃
    refine ⟨?_, ?_⟩
    · simp only [evaluate, ih₁.1, ih₂.1, ih₃.1]
    · intro v h
      simp only [evaluate] at h
      cases hx₁ : evaluate x₁ req es₁ <;> simp only [hx₁, Result.as, bind, Except.bind, reduceCtorEq] at h
      rename_i v₁
      cases hb : (Coe.coe v₁ : Result Bool) <;> simp only [hb, reduceCtorEq] at h
      rename_i b
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
      · exact ih₃.2 v h
      · exact ih₂.2 v h
  | and x₁ x₂ =>
    simp only [Expr.literalUIDs] at hlits
    have ⟨h₁, h₂⟩ := forall_mem_union hlits
    have ih₁ := evaluate_agree_safe x₁ hagree hstore hreq h₁
    have ih₂ := evaluate_agree_safe x₂ hagree hstore hreq h₂
    refine ⟨?_, ?_⟩
    · simp only [evaluate, ih₁.1, ih₂.1]
    · intro v h
      simp only [evaluate] at h
      cases hx₁ : evaluate x₁ req es₁ <;> simp only [hx₁, Result.as, bind, Except.bind, reduceCtorEq] at h
      rename_i v₁
      cases hb : (Coe.coe v₁ : Result Bool) <;> simp only [hb, reduceCtorEq] at h
      rename_i b
      cases b <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        pure, Except.pure, Except.ok.injEq] at h
      · subst h; exact .bool _
      · cases hx₂ : evaluate x₂ req es₁ <;> simp only [hx₂, reduceCtorEq] at h
        rename_i v₂
        cases hb₂ : (Coe.coe v₂ : Result Bool) <;>
          simp only [hb₂, reduceCtorEq, Except.ok.injEq] at h
        subst h; exact .bool _
  | or x₁ x₂ =>
    simp only [Expr.literalUIDs] at hlits
    have ⟨h₁, h₂⟩ := forall_mem_union hlits
    have ih₁ := evaluate_agree_safe x₁ hagree hstore hreq h₁
    have ih₂ := evaluate_agree_safe x₂ hagree hstore hreq h₂
    refine ⟨?_, ?_⟩
    · simp only [evaluate, ih₁.1, ih₂.1]
    · intro v h
      simp only [evaluate] at h
      cases hx₁ : evaluate x₁ req es₁ <;> simp only [hx₁, Result.as, bind, Except.bind, reduceCtorEq] at h
      rename_i v₁
      cases hb : (Coe.coe v₁ : Result Bool) <;> simp only [hb, reduceCtorEq] at h
      rename_i b
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      · cases hx₂ : evaluate x₂ req es₁ <;> simp only [hx₂, reduceCtorEq] at h
        rename_i v₂
        cases hb₂ : (Coe.coe v₂ : Result Bool) <;>
          simp only [hb₂, reduceCtorEq, Except.ok.injEq] at h
        subst h; exact .bool _
      · subst h; exact .bool _
  | unaryApp op x₁ =>
    simp only [Expr.literalUIDs] at hlits
    have ih₁ := evaluate_agree_safe x₁ hagree hstore hreq hlits
    refine ⟨?_, ?_⟩
    · simp only [evaluate, ih₁.1]
    · intro v h
      simp only [evaluate] at h
      cases hx₁ : evaluate x₁ req es₁ <;> simp only [hx₁, bind, Except.bind, reduceCtorEq] at h
      exact apply₁_safe h
  | binaryApp op x₁ x₂ =>
    simp only [Expr.literalUIDs] at hlits
    have ⟨h₁, h₂⟩ := forall_mem_union hlits
    have ih₁ := evaluate_agree_safe x₁ hagree hstore hreq h₁
    have ih₂ := evaluate_agree_safe x₂ hagree hstore hreq h₂
    refine ⟨?_, ?_⟩
    · simp only [evaluate, ← ih₁.1, ← ih₂.1]
      cases hx₁ : evaluate x₁ req es₁ <;> simp only [bind, Except.bind]
      cases evaluate x₂ req es₁ <;> simp only
      exact apply₂_agree hagree (ih₁.2 _ hx₁)
    · intro v h
      simp only [evaluate] at h
      cases hx₁ : evaluate x₁ req es₁ <;> simp only [hx₁, bind, Except.bind, reduceCtorEq] at h
      cases hx₂ : evaluate x₂ req es₁ <;> simp only [hx₂, reduceCtorEq] at h
      exact apply₂_safe hstore h
  | getAttr x₁ a =>
    simp only [Expr.literalUIDs] at hlits
    have ih₁ := evaluate_agree_safe x₁ hagree hstore hreq hlits
    refine ⟨?_, ?_⟩
    · simp only [evaluate, ← ih₁.1]
      cases hx₁ : evaluate x₁ req es₁ <;> simp only [bind, Except.bind]
      exact getAttr_agree hagree (ih₁.2 _ hx₁)
    · intro v h
      simp only [evaluate] at h
      cases hx₁ : evaluate x₁ req es₁ <;> simp only [hx₁, bind, Except.bind, reduceCtorEq] at h
      exact getAttr_safe hstore (ih₁.2 _ hx₁) h
  | hasAttr x₁ a =>
    simp only [Expr.literalUIDs] at hlits
    have ih₁ := evaluate_agree_safe x₁ hagree hstore hreq hlits
    refine ⟨?_, ?_⟩
    · simp only [evaluate, ← ih₁.1]
      cases hx₁ : evaluate x₁ req es₁ <;> simp only [bind, Except.bind]
      exact hasAttr_agree hagree (ih₁.2 _ hx₁)
    · intro v h
      simp only [evaluate] at h
      cases hx₁ : evaluate x₁ req es₁ <;> simp only [hx₁, bind, Except.bind, reduceCtorEq] at h
      exact hasAttr_safe h
  | extHasAttr x₁ a rest =>
    simp only [Expr.literalUIDs] at hlits
    have ih₁ := evaluate_agree_safe x₁ hagree hstore hreq hlits
    refine ⟨?_, ?_⟩
    · simp only [evaluate, ← ih₁.1]
      cases hx₁ : evaluate x₁ req es₁ <;> simp only [bind, Except.bind]
      exact hasAttrs_agree hagree hstore (ih₁.2 _ hx₁)
    · intro v h
      simp only [evaluate] at h
      cases hx₁ : evaluate x₁ req es₁ <;> simp only [hx₁, bind, Except.bind, reduceCtorEq] at h
      exact hasAttrs_safe h
  | set xs =>
    have ih : ∀ x ∈ xs, EvalAgreeSafe safe x req es₁ es₂ := by
      intro x hx
      have _ : sizeOf x < sizeOf (Expr.set xs) := by
        have h₁ := List.sizeOf_lt_of_mem hx
        simp only [Expr.set.sizeOf_spec]
        omega
      exact evaluate_agree_safe x hagree hstore hreq
        (fun u hu => hlits u (literalUIDs_set_mem hx hu))
    simp only [evaluate, xs.mapM₁_eq_mapM (evaluate · req es₁),
      xs.mapM₁_eq_mapM (evaluate · req es₂)]
    refine ⟨?_, ?_⟩
    · rw [List.mapM_congr (fun x hx => (ih x hx).1)]
    · intro v h
      cases hm : xs.mapM (evaluate · req es₁) <;> simp only [hm, bind, Except.bind, reduceCtorEq, Except.ok.injEq] at h
      rename_i vs
      subst h
      apply Value.Safe.set
      intro v hv
      rw [Set.mem_make] at hv
      obtain ⟨x, hx, hxv⟩ := List.mapM_ok_implies_all_from_ok hm v hv
      exact (ih x hx).2 v hxv
  | call xfn xs =>
    have ih : ∀ x ∈ xs, EvalAgreeSafe safe x req es₁ es₂ := by
      intro x hx
      have _ : sizeOf x < sizeOf (Expr.call xfn xs) := by
        have h₁ := List.sizeOf_lt_of_mem hx
        simp only [Expr.call.sizeOf_spec]
        omega
      exact evaluate_agree_safe x hagree hstore hreq
        (fun u hu => hlits u (literalUIDs_call_mem hx hu))
    simp only [evaluate, xs.mapM₁_eq_mapM (evaluate · req es₁),
      xs.mapM₁_eq_mapM (evaluate · req es₂)]
    refine ⟨?_, ?_⟩
    · rw [List.mapM_congr (fun x hx => (ih x hx).1)]
    · intro v h
      cases hm : xs.mapM (evaluate · req es₁) <;> simp only [hm, bind, Except.bind, reduceCtorEq] at h
      exact call_safe h
  | record axs =>
    have ih : ∀ ax ∈ axs, EvalAgreeSafe safe ax.snd req es₁ es₂ := by
      intro ax hx
      have _ : sizeOf ax.snd < sizeOf (Expr.record axs) := by
        have h₁ := List.sizeOf_lt_of_mem hx
        rw [Prod.mk.sizeOf_spec] at h₁
        simp only [Expr.record.sizeOf_spec]
        omega
      exact evaluate_agree_safe ax.snd hagree hstore hreq
        (fun u hu => hlits u (literalUIDs_record_mem hx hu))
    simp only [evaluate, bindAttr, pure, Except.pure]
    simp only [List.mapM₂_eq_mapM (λ x : (Attr × Expr) => do let v ← evaluate x.snd req es₁; .ok (x.fst, v))]
    simp only [List.mapM₂_eq_mapM (λ x : (Attr × Expr) => do let v ← evaluate x.snd req es₂; .ok (x.fst, v))]
    refine ⟨?_, ?_⟩
    · rw [List.mapM_congr
        (g := λ x : (Attr × Expr) => do let v ← evaluate x.snd req es₂; .ok (x.fst, v))
        (fun ax hx => by simp only [(ih ax hx).1])]
    · intro v h
      simp only [bind, Except.bind] at h
      split at h
      · simp at h
      rename_i avs hm
      simp only [Except.ok.injEq] at h
      subst h
      apply Value.Safe.record
      intro k v hk
      have hmem := Map.mem_make_mem_list (Map.find?_mem_toList hk)
      obtain ⟨ax, hx, hax⟩ := List.mapM_ok_implies_all_from_ok hm (k, v) hmem
      cases hev : evaluate ax.snd req es₁ <;> simp only [hev, reduceCtorEq, Except.ok.injEq] at hax
      rename_i v'
      have : v' = v := (Prod.mk.inj hax).2
      subst this
      exact (ih ax hx).2 v' hev
termination_by x

----- Policies -----

/-- Evaluating `x` gives the same result on both stores. -/
def EvalAgree (x : Expr) (req : Request) (es₁ es₂ : Entities) : Prop :=
  evaluate x req es₁ = evaluate x req es₂

theorem evalAgree_and {x₁ x₂ : Expr}
    (h₁ : EvalAgree x₁ req es₁ es₂) (h₂ : EvalAgree x₂ req es₁ es₂) :
    EvalAgree (.and x₁ x₂) req es₁ es₂ := by
  unfold EvalAgree at *
  simp only [evaluate, h₁, h₂]

theorem evalAgree_unaryApp {op : UnaryOp} {x : Expr} (h : EvalAgree x req es₁ es₂) :
    EvalAgree (.unaryApp op x) req es₁ es₂ := by
  unfold EvalAgree at *
  simp only [evaluate, h]

/-- A binary operator agrees when its first operand agrees and is safe and its
    second operand merely agrees. The second operand may contain unsafe
    literals: `apply₂` only reads the store at its first operand. -/
theorem evalAgree_binaryApp {op : BinaryOp} {x₁ x₂ : Expr}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u)
    (h₁ : EvalAgreeSafe safe x₁ req es₁ es₂) (h₂ : EvalAgree x₂ req es₁ es₂) :
    EvalAgree (.binaryApp op x₁ x₂) req es₁ es₂ := by
  unfold EvalAgree at *
  simp only [evaluate, ← h₁.1, ← h₂]
  cases hx₁ : evaluate x₁ req es₁ <;> simp only [bind, Except.bind]
  cases evaluate x₂ req es₁ <;> simp only
  exact apply₂_agree hagree (h₁.2 _ hx₁)

theorem evalAgree_lit {p : Prim} : EvalAgree (.lit p) req es₁ es₂ := by
  simp only [EvalAgree, evaluate]

theorem evalAgree_set_lits {uids : List EntityUID} :
    EvalAgree (.set (uids.map fun u => .lit (.entityUID u))) req es₁ es₂ := by
  unfold EvalAgree
  simp only [evaluate, List.mapM₁_eq_mapM (evaluate · req es₁), List.mapM₁_eq_mapM (evaluate · req es₂)]
  rw [List.mapM_congr (g := (evaluate · req es₂)) (fun x hx => by
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
    simp only [evaluate])]

theorem evalAgreeSafe_var {v : Var}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hstore : StoreSafe safe es₁)
    (hreq : RequestSafe safe req) :
    EvalAgreeSafe safe (.var v) req es₁ es₂ :=
  evaluate_agree_safe (.var v) hagree hstore hreq (by simp [Expr.literalUIDs, Set.not_mem_empty])

theorem scope_evalAgree {sc : Scope} {v : Var}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hstore : StoreSafe safe es₁)
    (hreq : RequestSafe safe req) :
    EvalAgree (sc.toExpr v) req es₁ es₂ := by
  have hv := evalAgreeSafe_var (v := v) hagree hstore hreq
  have his : ∀ ety, EvalAgree (v.isEntityType ety) req es₁ es₂ :=
    fun _ => evalAgree_unaryApp hv.1
  have hin : ∀ uid, EvalAgree (v.inEntityUID uid) req es₁ es₂ :=
    fun _ => evalAgree_binaryApp hagree hv evalAgree_lit
  cases sc with
  | any => exact evalAgree_lit
  | eq uid => exact evalAgree_binaryApp hagree hv evalAgree_lit
  | mem uid => exact hin uid
  | is ety => exact his ety
  | isMem ety uid => exact evalAgree_and (his ety) (hin uid)

theorem actionScope_evalAgree {asc : ActionScope}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hstore : StoreSafe safe es₁)
    (hreq : RequestSafe safe req) :
    EvalAgree asc.toExpr req es₁ es₂ := by
  cases asc with
  | actionScope sc => exact scope_evalAgree hagree hstore hreq
  | actionInAny uids =>
    exact evalAgree_binaryApp hagree (evalAgreeSafe_var hagree hstore hreq) evalAgree_set_lits

theorem conditions_foldl_evalAgree {l : List Condition} {acc : Expr}
    (hacc : EvalAgree acc req es₁ es₂) (hl : ∀ c ∈ l, EvalAgree c.toExpr req es₁ es₂) :
    EvalAgree (l.foldl (λ expr c => .and c.toExpr expr) acc) req es₁ es₂ := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons c l ih =>
    simp only [List.foldl_cons]
    exact ih (evalAgree_and (hl c (List.mem_cons_self ..)) hacc)
      (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'))

theorem conditions_evalAgree {cs : Conditions}
    (h : ∀ c ∈ cs, EvalAgree c.body req es₁ es₂) :
    EvalAgree cs.toExpr req es₁ es₂ := by
  have hc : ∀ c ∈ cs.reverse, EvalAgree c.toExpr req es₁ es₂ := by
    intro c hc
    have hb := h c (List.mem_reverse.mp hc)
    unfold Condition.toExpr
    cases c.kind
    · exact hb
    · exact evalAgree_unaryApp hb
  unfold Conditions.toExpr
  generalize cs.reverse = l at hc ⊢
  cases l with
  | nil => exact evalAgree_lit
  | cons c l =>
    exact conditions_foldl_evalAgree (hc c (List.mem_cons_self ..))
      (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc'))

/-- A policy evaluates the same on both stores when the literals in its
    `when`/`unless` bodies are safe. Literals in its scope may be unsafe. -/
theorem policy_evalAgree {p : Policy}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hstore : StoreSafe safe es₁)
    (hreq : RequestSafe safe req)
    (hlits : ∀ c ∈ p.condition, ∀ u ∈ c.body.literalUIDs, safe u) :
    EvalAgree p.toExpr req es₁ es₂ := by
  unfold Policy.toExpr PrincipalScope.toExpr ResourceScope.toExpr
  exact evalAgree_and (scope_evalAgree hagree hstore hreq)
    (evalAgree_and (actionScope_evalAgree hagree hstore hreq)
      (evalAgree_and (scope_evalAgree hagree hstore hreq)
        (conditions_evalAgree fun c hc =>
          (evaluate_agree_safe c.body hagree hstore hreq (hlits c hc)).1)))

/-- Authorization gives the same response on both stores when every policy's
    `when`/`unless` literals are safe. -/
theorem isAuthorized_agree {ps : Policies}
    (hagree : ∀ u, safe u → es₁.find? u = es₂.find? u) (hstore : StoreSafe safe es₁)
    (hreq : RequestSafe safe req)
    (hlits : ∀ p ∈ ps, ∀ c ∈ p.condition, ∀ u ∈ c.body.literalUIDs, safe u) :
    isAuthorized req es₁ ps = isAuthorized req es₂ ps :=
  Cedar.Thm.is_authorized_congr_evaluate fun p hp =>
    policy_evalAgree hagree hstore hreq (hlits p hp)

end

end Cedar.Validation
