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
import Cedar.TPE.Residual

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

inductive Error where
  | evaluation (err : Spec.Error)
  | invalidPolicy (err : TypeError)
  | invalidEnvironment
  | invalidRequestOrEntities
deriving Repr, Inhabited, DecidableEq

instance : Coe Spec.Error Error where
  coe := Error.evaluation

def PartialValue.asResidual (pv : PartialValue) (base : Residual) (ty : CedarType) : Residual :=
  .val (PartialValue.toResidualValue base pv ty) ty

/- Convert an optional value to a residual: Return `.error ty` when it's none -/
def someOrError : Option Value → CedarType → Residual
  | .some v, ty => .val v.asResidualValue ty
  | .none,   ty => .error ty

/- Convert an optional value to a residual: Return `self` when it's none -/
def someOrSelf : Option Value → CedarType → Residual → Residual
  | .some v, ty, _   => .val v.asResidualValue ty
  | .none,   _, self => self

def varₚ (req : PartialRequest) (var : Var) (ty : CedarType) : Residual :=
  match var with
  | .principal => varₒ req.principal.asEntityUID
  | .resource  => varₒ req.resource.asEntityUID
  | .action    => varₒ req.action
  | .context   => req.context >>= (PartialValue.record · |>.asResidual (.var .context ty) ty)|>.getD (.var .context ty)
where
  varₒ := (someOrSelf · ty (.var var ty))

def ite (c t e : Residual) (ty : CedarType) : Residual :=
  match c with
  | .val (.prim (.bool b)) _ => if b then t else e
  | .error _                 => .error ty
  | _                        => .ite c t e ty

def and : Residual → Residual → CedarType → Residual
  | .val (.prim (.bool true))  _, r, _ => r
  | .val (.prim (.bool false)) _, _, _ => false
  | .error _, _, ty    => .error ty
  | l, .val (.prim (.bool true)) _, _  => l
  | l, .val (.prim (.bool false)) rty, ty  =>
    if l.errorFree then false else .and l (.val (.prim (.bool false)) rty) ty
  | l, r, ty           => .and l r ty

def or : Residual → Residual → CedarType → Residual
  | .val (.prim (.bool true))  _, _, _ => true
  | .val (.prim (.bool false)) _, r, _ => r
  | .error _, _, ty    => .error ty
  | l, .val (.prim (.bool false)) _, _ => l
  | l, .val (.prim (.bool true)) rty, ty  =>
    if l.errorFree then true else .or l (.val (.prim (.bool true)) rty) ty
  | l, r, ty           => .or l r ty

def apply₁ (op₁ : UnaryOp) (r : Residual) (ty : CedarType) : Residual :=
  match r.asResidualValue with
  | .some v =>
    match op₁, v with
    | .not, .prim (.bool b) =>
      .val (!b) ty
    | .neg, .prim (.int i) =>
      someOrError (i.neg?) ty
    | .isEmpty, .set s =>
      .val s.isEmpty ty
    | .like p, .prim (.string s) =>
      .val (wildcardMatch s p) ty
    | .is ety, .prim (.entityUID uid) =>
      .val (ety == uid.ty) ty
    | _, _ => .error ty
  | .none =>
    match r with
    | .error _ => .error ty
    | _ => .unaryApp op₁ r ty

def inₑ (uid₁ uid₂ : EntityUID) (es : PartialEntities) : Option Bool :=
  if uid₁ = uid₂ then .some true else (es.ancestors uid₁).map (Set.contains · uid₂)

def inₛ (uid : EntityUID) (vs : Set Value) (es : PartialEntities): Option Bool := do
  (← vs.toList.mapM (Except.toOption ∘ Value.asEntityUID)).anyM (inₑ uid · es)

def hasTag (uid : EntityUID) (tag : String) (es : PartialEntities) : Option Bool :=
  (es.tags uid).map (Map.contains · tag)

def getTag (uid : EntityUID) (tag : String) (es : PartialEntities) (ty : CedarType) : Residual :=
  match es.tags uid with
  | .some tags =>
    match tags.find? tag with
    | .some (.present tv) => tv.asResidual (.val (.prim (.entityUID uid)) (.entity uid.ty)) ty
    | .some _ => .binaryApp .getTag uid tag ty
    | .none => .error ty
  | .none => .binaryApp .getTag uid tag ty

def apply₂ (op₂ : BinaryOp) (r₁ r₂ : Residual) (es : PartialEntities) (ty : CedarType) : Residual :=
  match r₁.asResidualValue, r₂.asResidualValue with
  | .some v₁, .some v₂ =>
    match op₂, v₁, v₂ with
    -- TODO: can be more precise, but may have to leave residual
    | .eq, (.record _), (.record _) => self
    | .eq, _, _ =>
      .val (v₁ == v₂) ty
    | .less, .prim (.int i), .prim (.int j) =>
      .val (i < j : Bool) ty
    | .less, .ext (.datetime d₁), .ext (.datetime d₂) =>
      .val (d₁ < d₂: Bool) ty
    | .less, .ext (.duration d₁), .ext (.duration d₂) =>
      .val (d₁ < d₂: Bool) ty
    | .lessEq, .prim (.int i), .prim (.int j) =>
      .val (i ≤ j : Bool) ty
    | .lessEq, .ext (.datetime d₁), .ext (.datetime d₂) =>
      .val (d₁ ≤ d₂: Bool) ty
    | .lessEq, .ext (.duration d₁), .ext (.duration d₂) =>
      .val (d₁ ≤ d₂: Bool) ty
    | .add, .prim (.int i), .prim (.int j) =>
      someOrError (i.add? j) ty
    | .sub, .prim (.int i), .prim (.int j) =>
      someOrError (i.sub? j) ty
    | .mul, .prim (.int i), .prim (.int j) =>
      someOrError (i.mul? j) ty
    -- TODO: can be more precise, but may have to leave residual
    | .contains, .set _, (.record _) => self
    | .contains, .set vs₁, _ =>
      .val (vs₁.contains (v₂.asValue.getD false)) ty
    | .containsAll, .set vs₁, .set vs₂ =>
      .val (vs₂.subset vs₁) ty
    | .containsAny, .set vs₁, .set vs₂ =>
      .val (vs₁.intersects vs₂) ty
    | .mem, .prim (.entityUID uid₁), .prim (.entityUID uid₂) =>
      someOrSelf (inₑ uid₁ uid₂ es) ty self
    | .mem, .prim (.entityUID uid₁), .set vs =>
      someOrSelf (inₛ uid₁ vs es) ty self
    | .hasTag, .prim (.entityUID uid₁), .prim (.string tag) =>
      someOrSelf (hasTag uid₁ tag es) ty self
    | .getTag, .prim (.entityUID uid₁), .prim (.string tag) =>
      getTag uid₁ tag es ty
    | _, _, _ => .error ty
  | _, _ =>
    match r₁, r₂ with
    | .error _, _ | _, .error _ => .error ty
    | _, _ => self
  where
  @[simp] self := .binaryApp op₂ r₁ r₂ ty

def hasAttr (r : Residual) (a : Attr) (es : PartialEntities) (ty : CedarType) : Residual :=
  match r with
  | .error _ => .error ty
  | .val (.record m) _ =>
    match m.find? a with
    | some (.present _) => true
    | some (.unknown tgt _) => .hasAttr tgt a ty
    | none => false
  | .val (.prim (.entityUID uid)) _ =>
    match es.attrs uid with
    | .some attrs =>
      match Map.find? attrs a with
      | .some (.present _) => true
      | .some (.unknown _) => .hasAttr r a ty
      | .none => false
    | .none => .hasAttr r a ty
  | _ => .hasAttr r a ty

def getAttr (r : Residual) (a : Attr) (es : PartialEntities) (ty : CedarType) : Residual :=
  match r with
  | .error _ => .error ty
  | .val (.record m) _ =>
    match m.find? a with
    | some (.present pv) => .val pv ty
    | some (.unknown tgt _) => .getAttr tgt a ty
    | none => .getAttr r a ty
  | .val (.prim (.entityUID uid)) _ =>
    match es.attrs uid with
    | .some attrs =>
      match Map.find? attrs a with
      | .some (.present pv) => .val (PartialValue.toResidualValue r pv ty) ty
      | .some (.unknown _) => .getAttr r a ty
      | .none => .getAttr r a ty
    | .none => .getAttr r a ty
  | _ => .getAttr r a ty

def set (rs : List Residual) (ty : CedarType) : Residual :=
  match rs.mapM Residual.asValue with
  | .some xs => .val (.set (Set.make xs)) ty
  | .none    => if rs.any Residual.isError then .error ty else .set rs ty

def record (m : List (Attr × Residual)) (ty : CedarType) : Residual :=
  match m.mapM λ (a, r₁) => bindAttr a (ResidualAttribute.present <$> r₁.asResidualValue) with
  | .some xs => .val (.record (Map.make xs)) ty
  | .none    => if m.any λ (_, r₁) => r₁.isError then .error ty else .record m ty

def call (xfn : ExtFun) (rs : List Residual) (ty : CedarType) : Residual :=
  match rs.mapM Residual.asValue with
  | .some xs => someOrError (Spec.call xfn xs).toOption ty
  | .none    => if rs.any Residual.isError then .error ty else .call xfn rs ty

def evaluate
  (x : Residual)
  (req : PartialRequest)
  (es : PartialEntities) : Residual :=
  match x with
  | .val l ty => .val l ty
  | .var v ty => varₚ req v ty
  | .error ty => .error ty
  | .ite x₁ x₂ x₃ ty =>
    ite (evaluate x₁ req es) (evaluate x₂ req es) (evaluate x₃ req es) ty
  | .and x₁ x₂ ty =>
    and (evaluate x₁ req es) (evaluate x₂ req es) ty
  | .or x₁ x₂ ty =>
    or (evaluate x₁ req es) (evaluate x₂ req es) ty
  | .unaryApp op₁ x₁ ty =>
    apply₁ op₁ (evaluate x₁ req es) ty
  | .binaryApp op₂ x₁ x₂ ty =>
    apply₂ op₂ (evaluate x₁ req es) (evaluate x₂ req es) es ty
  | .hasAttr x₁ a ty =>
    hasAttr (evaluate x₁ req es) a es ty
  | .getAttr x₁ a ty =>
    getAttr (evaluate x₁ req es) a es ty
  | .set xs ty =>
    set (xs.map₁ (λ ⟨x₁, _⟩ => evaluate x₁ req es)) ty
  | .record axs ty =>
    record (axs.map₁ (λ ⟨(a, x₁), _⟩ => (a, evaluate x₁ req es))) ty
  | .call xfn xs ty =>
    call xfn (xs.map₁ (λ ⟨x₁, _⟩ => evaluate x₁ req es)) ty
termination_by x
decreasing_by
  all_goals
    simp_wf
    try omega
  any_goals
    rename_i h
    replace h := List.sizeOf_lt_of_mem h
    try simp at h
    omega

open Cedar.Spec Cedar.Validation

/-- Partially evaluating a policy.
Note that this function actually evaluates a type-lifted version of `TypedExpr`
produced by the type checker, as opposed to evaluating the expression directly.
This design is to simplify proofs otherwise we need to prove theorems that
state type-lifting (i.e, `TypedExpr.liftBoolTypes`) do not change the results
of evaluating residuals. The soundness theorem still holds. That is,
reauthorizing the residuals produces the same outcome as authorizing the input
expressions with consistent requests/entities. It is just that the types in the
residuals are all lifted. We essentially trade efficiency for ease of proofs,
which I (Shaobo) think is fine because the Lean model is a reference model not
used in production.
-/
def evaluatePolicy (schema : Schema)
  (p : Policy)
  (req : PartialRequest)
  (es : PartialEntities)
  : Except Error Residual :=
  match schema.environment? req.principal.ty req.resource.ty req.action with
    | .some env =>
      if requestAndEntitiesIsValid env req es
      then
        do
          let expr := substituteAction env.reqty.action p.toExpr
          let (te, _) ← (typeOf expr ∅ env).mapError Error.invalidPolicy
          .ok (evaluate te.liftBoolTypes.toResidual req es)
      else .error .invalidRequestOrEntities
    | .none => .error .invalidEnvironment

/-! ## Test fixtures -/

private def emptyReq : PartialRequest := ⟨⟨default, none⟩, default, ⟨default, none⟩, none⟩
private def emptyEs  : PartialEntities := default
private def ety      : EntityType := ⟨"User", []⟩

-- Helper: wrap an EntityUID as a Residual value
private def entityVal (uid : EntityUID) : Residual :=
  .val (.prim (.entityUID uid)) (.entity uid.ty)

/-! ## 1. Smoke tests (non-attribute operations) -/

-- A literal value evaluates to itself.
#guard evaluate (.val true (.bool .anyBool)) emptyReq emptyEs
    = .val true (.bool .anyBool)

-- A fully-known binary op reduces to a value.
#guard evaluate (.binaryApp .eq (.val (.prim (.int 1)) .int) (.val (.prim (.int 1)) .int) (.bool .anyBool)) emptyReq emptyEs
    = .val true (.bool .anyBool)

/-! ## 3. Unresolved receiver (non-value residual)

    When the receiver doesn't reduce to a value (e.g., an unknown var),
    hasAttr/getAttr cannot make progress and must return a residual.

    emptyReq has context = none, so `.var .context ty` stays as-is after evaluate.
-/

private def ctxTy  : CedarType := .record (Map.make [("x", .required .int)])
private def ctxVar : Residual  := .var .context ctxTy

-- hasAttr on an unresolved var  →  residual (no information to decide)
#guard evaluate (.hasAttr ctxVar "x" (.bool .anyBool)) emptyReq emptyEs
    = .hasAttr ctxVar "x" (.bool .anyBool)

-- getAttr on an unresolved var  →  residual
#guard evaluate (.getAttr ctxVar "x" .int) emptyReq emptyEs
    = .getAttr ctxVar "x" .int

-- principal/resource are also unknown in emptyReq (id = none), so they stay as vars.
#guard evaluate (.hasAttr (.var .principal (.entity ety)) "role" (.bool .anyBool)) emptyReq emptyEs
    = .hasAttr (.var .principal (.entity ety)) "role" (.bool .anyBool)

#guard evaluate (.getAttr (.var .principal (.entity ety)) "role" .string) emptyReq emptyEs
    = .getAttr (.var .principal (.entity ety)) "role" .string

#guard evaluate (.getAttr (.var .resource (.entity ety)) "owner" (.entity ety)) emptyReq emptyEs
    = .getAttr (.var .resource (.entity ety)) "owner" (.entity ety)

/-! ## 4. Record literals

    A `.val (.record m)` is a fully-constructed record. The attribute map `m`
    contains `ResidualAttribute` entries that are either `.present` or `.unknown`.
-/

/-! ### 4a. All-present record -/

-- record = { "a" : 42 }
private def recAllPresent : Residual :=
  .val (.record (Map.make [("a", .present (.prim (.int 42)))]))
       (.record (Map.make [("a", .required .int)]))

-- hasAttr for a present key  →  true
#guard evaluate (.hasAttr recAllPresent "a" (.bool .anyBool)) emptyReq emptyEs
    = .val true (.bool .anyBool)

-- getAttr for a present key  →  the value
#guard evaluate (.getAttr recAllPresent "a" .int) emptyReq emptyEs
    = .val (.prim (.int 42)) .int

/-! ### 4b. Record with a mix of present and unknown attributes -/

-- record = { "k" : true, "u" : <unknown, target = principal> }
-- The unknown attribute stores a target residual that represents where the
-- value would come from at full-evaluation time.
private def unknownTgt : Residual := .var .principal (.entity ety)
private def recMixed   : Residual :=
  .val (.record (Map.make [ ("k", .present (.prim (.bool true)))
                , ("u", .unknown unknownTgt .int) ]))
       (.record (Map.make [("k", .required (.bool .anyBool)), ("u", .required .int)]))

-- hasAttr "k" (present)  →  true
#guard evaluate (.hasAttr recMixed "k" (.bool .anyBool)) emptyReq emptyEs
    = .val true (.bool .anyBool)

-- getAttr "k" (present)  →  the value
#guard evaluate (.getAttr recMixed "k" (.bool .anyBool)) emptyReq emptyEs
    = .val (.prim (.bool true)) (.bool .anyBool)

-- hasAttr "u" (unknown)  →  residual delegated to the target
--   The unknown entry stores `unknownTgt` as the expression that would know
--   whether "u" exists, so we get `.hasAttr unknownTgt "u" ty`.
#guard evaluate (.hasAttr recMixed "u" (.bool .anyBool)) emptyReq emptyEs
    = .hasAttr unknownTgt "u" (.bool .anyBool)

-- getAttr "u" (unknown)  →  residual delegated to the target
#guard evaluate (.getAttr recMixed "u" .int) emptyReq emptyEs
    = .getAttr unknownTgt "u" .int

/-! ## 5. Entity attribute access

    When the receiver is `.val (.prim (.entityUID uid))`, hasAttr/getAttr look
    up `es.attrs uid` to get the entity's attribute map, then search for the
    attribute within it.

    Lookup chain:  es.find? uid  →  PartialEntityData.attrs  →  Map.find? attr
    If any step returns none, the overall result is none.
-/

/-! ### 5a. Entity with a mix of present and unknown attrs -/

-- alice has attrs = { "name" : present "Alice", "role" : unknown String }
private def alice    : EntityUID := ⟨ety, "alice"⟩
private def aliceVal : Residual  := entityVal alice
private def aliceEs  : PartialEntities := Map.make [(alice, ⟨
  some (Map.make [ ("name", PartialAttribute.present (PartialValue.prim (.string "Alice")))
                 , ("role", PartialAttribute.unknown .string) ]),
  none, none ⟩)]

-- hasAttr "name" (present)  →  true
#guard evaluate (.hasAttr aliceVal "name" (.bool .anyBool)) emptyReq aliceEs
    = .val true (.bool .anyBool)

-- getAttr "name" (present)  →  the value
#guard evaluate (.getAttr aliceVal "name" .string) emptyReq aliceEs
    = .val (.prim (.string "Alice")) .string

-- hasAttr "role" (unknown)  →  residual
--   The attr exists but its value is unknown, so we can't decide true/false.
#guard evaluate (.hasAttr aliceVal "role" (.bool .anyBool)) emptyReq aliceEs
    = .hasAttr aliceVal "role" (.bool .anyBool)

-- getAttr "role" (unknown)  →  residual
#guard evaluate (.getAttr aliceVal "role" .string) emptyReq aliceEs
    = .getAttr aliceVal "role" .string

-- hasAttr "missing" (not in map)  →  false
--   Map.find? returns none, which maps to false.
#guard evaluate (.hasAttr aliceVal "missing" (.bool .anyBool)) emptyReq aliceEs
    = .val false (.bool .anyBool)

/-! ### 5b. Entity not in the store at all -/

-- nobody is not in emptyEs, so es.find? returns none.
-- es.attrs returns none  →  >>= gives none  →  hasAttr maps none to false.
-- getAttr falls through to the default residual.
private def nobody    : EntityUID := ⟨ety, "nobody"⟩
private def nobodyVal : Residual  := entityVal nobody

#guard evaluate (.hasAttr nobodyVal "x" (.bool .anyBool)) emptyReq emptyEs
    = .hasAttr nobodyVal "x" (.bool .anyBool)

#guard evaluate (.getAttr nobodyVal "x" .int) emptyReq emptyEs
    = .getAttr nobodyVal "x" .int

/-! ### 5c. Entity in the store but with attrs = none (entirely unknown attrs) -/

-- dave exists in the store but his attribute map is none (not yet loaded).
-- es.find? succeeds, but PartialEntityData.attrs = none.
-- none >>= (Map.find? · a) = none  →  same as 5b.
private def dave    : EntityUID := ⟨ety, "dave"⟩
private def daveVal : Residual  := entityVal dave
private def daveEs  : PartialEntities := Map.make [(dave, ⟨none, none, none⟩)]

#guard evaluate (.hasAttr daveVal "x" (.bool .anyBool)) emptyReq daveEs
    = .hasAttr daveVal "x" (.bool .anyBool)

#guard evaluate (.getAttr daveVal "x" .int) emptyReq daveEs
    = .getAttr daveVal "x" .int

/-! ## 6. Nested attribute access through an unknown entity attribute

    bob has attrs = { "manager" : unknown (entity User) }.
    getAttr bob "manager" cannot resolve, so it stays as a residual.
    A further getAttr/hasAttr on that residual also stays unresolved.
-/

private def bob    : EntityUID := ⟨ety, "bob"⟩
private def bobVal : Residual  := entityVal bob
private def bobEs  : PartialEntities := Map.make [(bob, ⟨
  some (Map.make [("manager", PartialAttribute.unknown (.entity ety))]), none, none ⟩)]

-- getAttr bob "manager" is unknown  →  residual
private def bobManager : Residual := .getAttr bobVal "manager" (.entity ety)

#guard evaluate bobManager emptyReq bobEs
    = bobManager

-- getAttr (getAttr bob "manager") "name"  →  residual (chained unknown)
#guard evaluate (.getAttr bobManager "name" .string) emptyReq bobEs
    = .getAttr bobManager "name" .string

-- hasAttr (getAttr bob "manager") "name"  →  residual
#guard evaluate (.hasAttr bobManager "name" .string) emptyReq bobEs
    = .hasAttr bobManager "name" .string

/-! ## 7. Record-valued entity attribute with mixed known/unknown fields

    charlie has attrs = { "profile" : present { "email" : present "...",
                                                "age"   : unknown Int,
                                                "other" : unknown Int } }

    getAttr charlie "profile" resolves to a record value whose fields carry
    ResidualAttribute.unknown entries pointing back to the entity.
    A subsequent getAttr/hasAttr on that record for a known field resolves;
    for an unknown field it delegates back to the entity-level expression.
-/

private def charlie    : EntityUID := ⟨ety, "charlie"⟩
private def charlieVal : Residual  := entityVal charlie
private def charlieEs  : PartialEntities := Map.make [(charlie, ⟨
  some (Map.make [("profile", PartialAttribute.present (PartialValue.record (Map.make [
    ("email", PartialAttribute.present (PartialValue.prim (.string "charlie@example.com"))),
    ("age",   PartialAttribute.unknown .int),
    ("other", PartialAttribute.unknown .int) ])))]),
  none, none ⟩)]

private def profileTy      : CedarType := .record (Map.make [("email", .required .string), ("age", .required .int)])
private def getProfile      : Residual  := .getAttr charlieVal "profile" profileTy

-- First, verify what getProfile itself evaluates to.
-- charlie's "profile" is a present PartialValue.record. getAttr on a present
-- entity attr calls PartialValue.toResidualValue with target = charlieVal.
-- For each field in the PartialValue.record (sorted by key):
--   "age"   : PartialAttribute.unknown .int  →  ResidualAttribute.unknown charlieVal .int
--   "email" : PartialAttribute.present "…"   →  ResidualAttribute.present (.prim (.string "…"))
--   "other" : PartialAttribute.unknown .int  →  ResidualAttribute.unknown charlieVal .int
-- The result is a .val (.record …) at profileTy.
#guard evaluate getProfile emptyReq charlieEs
    = .val (.record (Map.make [ ("age",   .unknown charlieVal .int)
                    , ("email", .present (.prim (.string "charlie@example.com")))
                    , ("other", .unknown charlieVal .int) ]))
           profileTy

-- getAttr profile "email" (present in the nested record)  →  the value
--   profile resolves to a record; "email" is .present, so we get the string.
#guard evaluate (.getAttr getProfile "email" .string) emptyReq charlieEs
    = .val (.prim (.string "charlie@example.com")) .string

-- getAttr profile "age" (unknown in the nested record)  →  entity-level residual
--   "age" is .unknown with target = charlieVal, so we get .getAttr charlieVal "age".
#guard evaluate (.getAttr getProfile "age" .int) emptyReq charlieEs
    = .getAttr charlieVal "age" .int

-- hasAttr profile "age" (unknown in the nested record)  →  entity-level residual
#guard evaluate (.hasAttr getProfile "age" (.bool .anyBool)) emptyReq charlieEs
    = .hasAttr charlieVal "age" (.bool .anyBool)

/-! ## 8. Deeply nested records

    eve has attrs = { "info" : present {
      "address" : present { "city" : present "Seattle", "zip" : unknown String },
      "score"   : unknown Int
    }}

    This exercises toResidualValue's recursive target-threading:
    - Outer record target = eveVal
    - "address" is present, so inner record target = .getAttr eveVal "address" outerTy
    - "score" is unknown, so it gets .unknown eveVal .int
    - Inside "address": "zip" is unknown, target = .getAttr eveVal "address" outerTy
      so it gets .unknown (.getAttr eveVal "address" outerTy) .string
-/

private def eve    : EntityUID := ⟨ety, "eve"⟩
private def eveVal : Residual  := entityVal eve

private def innerRecTy : CedarType := .record (Map.make [("city", .required .string), ("zip", .required .string)])
private def outerRecTy : CedarType := .record (Map.make [("address", .required innerRecTy), ("score", .required .int)])

private def eveEs : PartialEntities := Map.make [(eve, ⟨
  some (Map.make [("info", PartialAttribute.present (PartialValue.record (Map.make [
    ("address", PartialAttribute.present (PartialValue.record (Map.make [
      ("city", PartialAttribute.present (PartialValue.prim (.string "Seattle"))),
      ("zip",  PartialAttribute.unknown .string) ]))),
    ("score", PartialAttribute.unknown .int) ])))]),
  none, none ⟩)]

private def getInfo : Residual := .getAttr eveVal "info" outerRecTy

-- The target threaded into the inner "address" record is:
private def addressTarget : Residual := .getAttr eveVal "address" outerRecTy

-- Verify the shape of `evaluate getInfo`:
-- toResidualValue with target = eveVal produces:
--   "address" (present record) → recurse with target = .getAttr eveVal "address" outerRecTy
--     "city" (present) → .present (.prim (.string "Seattle"))
--     "zip"  (unknown) → .unknown addressTarget .string
--   "score" (unknown) → .unknown eveVal .int
#guard evaluate getInfo emptyReq eveEs
    = .val (.record (Map.make [ ("address", .present (.record (Map.make [ ("city", .present (.prim (.string "Seattle")))
                                                    , ("zip",  .unknown addressTarget .string) ])))
                    , ("score",   .unknown eveVal .int) ]))
           outerRecTy

-- getAttr info "score" (unknown at outer level)  →  .getAttr eveVal "score"
--   The outer record has .unknown eveVal .int for "score".
#guard evaluate (.getAttr getInfo "score" .int) emptyReq eveEs
    = .getAttr eveVal "score" .int

-- hasAttr info "score"  →  .hasAttr eveVal "score"
#guard evaluate (.hasAttr getInfo "score" (.bool .anyBool)) emptyReq eveEs
    = .hasAttr eveVal "score" (.bool .anyBool)

-- getAttr info "address" (present inner record)  →  the inner record value
private def getAddress : Residual := .getAttr getInfo "address" innerRecTy

#guard evaluate getAddress emptyReq eveEs
    = .val (.record (Map.make [ ("city", .present (.prim (.string "Seattle")))
                    , ("zip",  .unknown addressTarget .string) ]))
           innerRecTy

-- getAttr address "city" (present in inner record)  →  the value
#guard evaluate (.getAttr getAddress "city" .string) emptyReq eveEs
    = .val (.prim (.string "Seattle")) .string

-- getAttr address "zip" (unknown in inner record)  →  .getAttr addressTarget "zip"
--   The unknown entry's target is addressTarget = .getAttr eveVal "address" outerRecTy,
--   so we get a two-level getAttr chain back to the entity.
#guard evaluate (.getAttr getAddress "zip" .string) emptyReq eveEs
    = .getAttr addressTarget "zip" .string

-- hasAttr address "zip"  →  .hasAttr addressTarget "zip"
#guard evaluate (.hasAttr getAddress "zip" (.bool .anyBool)) emptyReq eveEs
    = .hasAttr addressTarget "zip" (.bool .anyBool)

-- hasAttr address "city" (present)  →  true
#guard evaluate (.hasAttr getAddress "city" (.bool .anyBool)) emptyReq eveEs
    = .val true (.bool .anyBool)

-- hasAttr address "nonexistent" (not in inner record)  →  false
#guard evaluate (.hasAttr getAddress "nonexistent" (.bool .anyBool)) emptyReq eveEs
    = .val false (.bool .anyBool)

end Cedar.TPE
