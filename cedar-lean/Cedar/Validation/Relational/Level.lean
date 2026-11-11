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

public import Cedar.Validation.Levels
public import Cedar.Validation.Relational.Policy

@[expose] public section

/-! # Relational specification of level-based validation

`ValidPolicyAtLevel ets acts envs n p` holds when `validateWithLevel [p] schema n` accepts `p`.
`LevelOk` mirrors `checkLevel` and `EntityAccessOk` mirrors `checkEntityAccessLevel`; since those
run on the typed expression, each rule reads the types it needs from `HasType` premises on the
subexpression it concerns. -/

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-- A Boolean type other than `.tt`. -/
inductive NotTt : BoolType → Prop where
  | ff : NotTt .ff
  | anyBool : NotTt .anyBool

/-- The binary operators whose left operand `checkLevel` treats as dereferenced. -/
inductive DerefOp : BinaryOp → Prop where
  | mem : DerefOp .mem
  | getTag : DerefOp .getTag
  | hasTag : DerefOp .hasTag

/-- The binary operators that dereference neither operand. -/
inductive NotDerefOp : BinaryOp → Prop where
  | eq : NotDerefOp .eq
  | less : NotDerefOp .less
  | lessEq : NotDerefOp .lessEq
  | add : NotDerefOp .add
  | sub : NotDerefOp .sub
  | mul : NotDerefOp .mul
  | contains : NotDerefOp .contains
  | containsAll : NotDerefOp .containsAll
  | containsAny : NotDerefOp .containsAny

/-- The first field named `a` of a record literal (`Map.find?` on the `Map.make` of the
    record's typed fields, which keeps the first of duplicate keys). -/
inductive RecordFieldFind : Attr → Expr → List (Attr × Expr) → Prop where
  | here : ∀ a x axs, RecordFieldFind a x ((a, x) :: axs)
  | there : ∀ a x a' x' axs, a ≠ a' → RecordFieldFind a x axs →
      RecordFieldFind a x ((a', x') :: axs)

mutual
/-- `checkLevel` on the expression `x` typed under capabilities `c`: every entity
    dereference in `x` is at most `n` dereferences away from a variable. -/
inductive LevelOk : Expr → Capabilities → TypeEnv → Nat → Prop where
  | lit : ∀ p c env n, LevelOk (.lit p) c env n
  | var : ∀ v c env n, LevelOk (.var v) c env n
  | iteTt : ∀ a b e c env n ca cca,
      HasType false false a c env (.bool .tt) ca → CapMerge c ca cca →
      LevelOk a c env n → LevelOk b cca env n →
      LevelOk (.ite a b e) c env n
  | iteFf : ∀ a b e c env n ca,
      HasType false false a c env (.bool .ff) ca →
      LevelOk a c env n → LevelOk e c env n →
      LevelOk (.ite a b e) c env n
  | iteAnyBool : ∀ a b e c env n ca cca,
      HasType false false a c env (.bool .anyBool) ca → CapMerge c ca cca →
      LevelOk a c env n → LevelOk b cca env n → LevelOk e c env n →
      LevelOk (.ite a b e) c env n
  | andFf : ∀ a b c env n ca,
      HasType false false a c env (.bool .ff) ca →
      LevelOk a c env n →
      LevelOk (.and a b) c env n
  | and : ∀ a b c env n ba ca cca,
      HasType false false a c env (.bool ba) ca → NotFf ba → CapMerge c ca cca →
      LevelOk a c env n → LevelOk b cca env n →
      LevelOk (.and a b) c env n
  | orTt : ∀ a b c env n ca,
      HasType false false a c env (.bool .tt) ca →
      LevelOk a c env n →
      LevelOk (.or a b) c env n
  | or : ∀ a b c env n ba ca,
      HasType false false a c env (.bool ba) ca → NotTt ba →
      LevelOk a c env n → LevelOk b c env n →
      LevelOk (.or a b) c env n
  | unaryApp : ∀ op a c env n, LevelOk a c env n → LevelOk (.unaryApp op a) c env n
  | binaryAppDeref : ∀ op a b c env n, DerefOp op →
      EntityAccessOk a c env n (n + 1) [] → LevelOk b c env (n + 1) →
      LevelOk (.binaryApp op a b) c env (n + 1)
  | binaryApp : ∀ op a b c env n, NotDerefOp op →
      LevelOk a c env n → LevelOk b c env n →
      LevelOk (.binaryApp op a b) c env n
  | getAttrEntity : ∀ a k c env n ety ca,
      HasType false false a c env (.entity ety) ca →
      EntityAccessOk a c env n (n + 1) [] →
      LevelOk (.getAttr a k) c env (n + 1)
  | getAttrRecord : ∀ a k c env n rty ca,
      HasType false false a c env (.record rty) ca →
      LevelOk a c env n →
      LevelOk (.getAttr a k) c env n
  | hasAttrEntity : ∀ a k c env n ety ca,
      HasType false false a c env (.entity ety) ca →
      EntityAccessOk a c env n (n + 1) [] →
      LevelOk (.hasAttr a k) c env (n + 1)
  | hasAttrRecord : ∀ a k c env n rty ca,
      HasType false false a c env (.record rty) ca →
      LevelOk a c env n →
      LevelOk (.hasAttr a k) c env n
  | extHasAttrEntity : ∀ a k ks c env n ety ca,
      HasType false false a c env (.entity ety) ca →
      extHasAttrChainCost env (.entity ety) (k :: ks) < n →
      EntityAccessOk a c env (n - extHasAttrChainCost env (.entity ety) (k :: ks) - 1) n [] →
      LevelOk (.extHasAttr a k ks) c env n
  | extHasAttrRecordPath : ∀ a k ks c env n rty ca path,
      HasType false false a c env (.record rty) ca →
      extHasAttrFirstEntityPath? env (.record rty) (k :: ks) = some path →
      EntityAccessOk a c env (n - extHasAttrChainCost env (.record rty) (k :: ks)) n path →
      extHasAttrChainCost env (.record rty) (k :: ks) ≤ n →
      LevelOk a c env n →
      LevelOk (.extHasAttr a k ks) c env n
  | extHasAttrRecordNoPath : ∀ a k ks c env n rty ca,
      HasType false false a c env (.record rty) ca →
      extHasAttrFirstEntityPath? env (.record rty) (k :: ks) = none →
      extHasAttrChainCost env (.record rty) (k :: ks) ≤ n →
      LevelOk a c env n →
      LevelOk (.extHasAttr a k ks) c env n
  | set : ∀ xs c env n, LevelOkList xs c env n → LevelOk (.set xs) c env n
  | record : ∀ axs c env n, LevelOkRecord axs c env n → LevelOk (.record axs) c env n
  | call : ∀ f xs c env n, LevelOkList xs c env n → LevelOk (.call f xs) c env n

/-- `checkEntityAccessLevel` on the expression `x` typed under capabilities `c`: `x` (or, for
    a nonempty `path`, the value at `path` within record `x`) is an entity that may be
    dereferenced `n` more times, with every other subexpression checked at level `nmax`. -/
inductive EntityAccessOk : Expr → Capabilities → TypeEnv → Nat → Nat → List Attr → Prop where
  | var : ∀ v c env n nmax path, EntityAccessOk (.var v) c env n nmax path
  | action : ∀ c ets acts p act r ctx n nmax path,
      EntityAccessOk (.lit (.entityUID act)) c ⟨ets, acts, ⟨p, act, r, ctx⟩⟩ n nmax path
  | iteTt : ∀ a b e c env n nmax path ca cca,
      HasType false false a c env (.bool .tt) ca → CapMerge c ca cca →
      LevelOk a c env nmax → EntityAccessOk b cca env n nmax path →
      EntityAccessOk (.ite a b e) c env n nmax path
  | iteFf : ∀ a b e c env n nmax path ca,
      HasType false false a c env (.bool .ff) ca →
      LevelOk a c env nmax → EntityAccessOk e c env n nmax path →
      EntityAccessOk (.ite a b e) c env n nmax path
  | iteAnyBool : ∀ a b e c env n nmax path ca cca,
      HasType false false a c env (.bool .anyBool) ca → CapMerge c ca cca →
      LevelOk a c env nmax → EntityAccessOk b cca env n nmax path →
      EntityAccessOk e c env n nmax path →
      EntityAccessOk (.ite a b e) c env n nmax path
  | andFf : ∀ a b c env n nmax path ca,
      HasType false false a c env (.bool .ff) ca →
      EntityAccessOk a c env n nmax path →
      EntityAccessOk (.and a b) c env n nmax path
  | orTt : ∀ a b c env n nmax path ca,
      HasType false false a c env (.bool .tt) ca →
      EntityAccessOk a c env n nmax path →
      EntityAccessOk (.or a b) c env n nmax path
  | getAttrEntity : ∀ a k c env n nmax path ety ca,
      HasType false false a c env (.entity ety) ca →
      EntityAccessOk a c env n nmax [] →
      EntityAccessOk (.getAttr a k) c env (n + 1) nmax path
  | getAttrRecord : ∀ a k c env n nmax path rty ca,
      HasType false false a c env (.record rty) ca →
      EntityAccessOk a c env n nmax (k :: path) →
      EntityAccessOk (.getAttr a k) c env n nmax path
  | getTag : ∀ a b c env n nmax path,
      EntityAccessOk a c env n nmax [] → LevelOk b c env nmax →
      EntityAccessOk (.binaryApp .getTag a b) c env (n + 1) nmax path
  | record : ∀ axs k x c env n nmax path,
      RecordFieldFind k x axs →
      EntityAccessOk x c env n nmax path →
      LevelOkRecord axs c env nmax →
      EntityAccessOk (.record axs) c env n nmax (k :: path)

/-- `LevelOk` for every expression of a list. -/
inductive LevelOkList : List Expr → Capabilities → TypeEnv → Nat → Prop where
  | nil : ∀ c env n, LevelOkList [] c env n
  | cons : ∀ x xs c env n, LevelOk x c env n → LevelOkList xs c env n →
      LevelOkList (x :: xs) c env n

/-- `LevelOk` for every field of a record literal. -/
inductive LevelOkRecord : List (Attr × Expr) → Capabilities → TypeEnv → Nat → Prop where
  | nil : ∀ c env n, LevelOkRecord [] c env n
  | cons : ∀ a x axs c env n, LevelOk x c env n → LevelOkRecord axs c env n →
      LevelOkRecord ((a, x) :: axs) c env n
end

/-! ## Validation at a level -/

/-- `TypedInEnvs`, additionally requiring the typed policy to pass the level check at `n` in
    each environment. -/
inductive TypedAtLevelInEnvs : List TypeEnv → Nat → Expr → List BoolType → Prop where
  | nil : ∀ n x, TypedAtLevelInEnvs [] n x []
  | cons : ∀ ets acts p act r ctx n x x' b cout envs bs,
      SubstAction act x x' →
      HasType false false x' [] ⟨ets, acts, ⟨p, act, r, ctx⟩⟩ (.bool b) cout →
      LevelOk x' [] ⟨ets, acts, ⟨p, act, r, ctx⟩⟩ n →
      TypedAtLevelInEnvs envs n x bs →
      TypedAtLevelInEnvs (⟨ets, acts, ⟨p, act, r, ctx⟩⟩ :: envs) n x (b :: bs)

/-- `validateWithLevel` accepts `p` at level `n` against `envs`, all sharing the schemas `ets`
    and `acts`. -/
inductive ValidPolicyAtLevel : EntitySchema → ActionSchema → List TypeEnv → Nat → Policy →
    Prop where
  | mk : ∀ ets acts envs n p x bs,
      PolicyExpr p x →
      EntitiesDeclared ets acts x →
      TypedAtLevelInEnvs envs n x bs →
      SomeNotFf bs →
      ValidPolicyAtLevel ets acts envs n p

end Cedar.Validation.Relational
