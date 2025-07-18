import Cedar.Spec
import Cedar.Data
import Cedar.TPE.Residual
import Cedar.TPE.Evaluator
import Cedar.TPE.Input

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation


/--
 Possible improvements
 - Some entities don't need to be loaded at all (User::"oliver" == User::"emina")
 - Never load ancestors- instead, ask if something is an ancestor of something else
  - Configurable: Fewer pulls if you load all ancestors
 - Analysis for how many calls to the entity loader there will be
-/

def EntityLoader : Type := Set EntityUID → Map EntityUID EntityData

def TypedExpr.allLiteralUIDs (x : TypedExpr) : Set EntityUID :=
  match x with
  | .lit l _ =>
    match l with
    | .entityUID id => Set.singleton id
    | _ => Set.empty
  | .var v _ =>
    -- these cases should not happen, since the request was fully concrete
    match v with
    | .principal => Set.empty
    | .resource  => Set.empty
    | .action    => Set.empty
    | .context   => Set.empty
  | .ite c t e _ => TypedExpr.allLiteralUIDs c ∪ TypedExpr.allLiteralUIDs t ∪ TypedExpr.allLiteralUIDs e
  | .and a b _   => TypedExpr.allLiteralUIDs a ∪ TypedExpr.allLiteralUIDs b
  | .or a b _    => TypedExpr.allLiteralUIDs a ∪ TypedExpr.allLiteralUIDs b
  | .unaryApp _ e _ => TypedExpr.allLiteralUIDs e
  | .binaryApp _ a b _ => TypedExpr.allLiteralUIDs a ∪ TypedExpr.allLiteralUIDs b
  | .getAttr e _ _ => TypedExpr.allLiteralUIDs e
  | .hasAttr e _ _ => TypedExpr.allLiteralUIDs e
  | .set ls _ => ls.mapUnion₁ (λ ⟨v, _⟩ => TypedExpr.allLiteralUIDs v)
  | .record m _ => m.mapUnion₂ (λ ⟨⟨_attr, v⟩, _⟩ => TypedExpr.allLiteralUIDs v)
  | .call _ ls _ => ls.mapUnion₁ (λ ⟨v, _⟩ => TypedExpr.allLiteralUIDs v)
termination_by sizeOf x
decreasing_by
  repeat case _ =>
    simp [*]; try omega
  . rename_i h
    let so := List.sizeOf_lt_of_mem h
    simp
    omega
  . rename_i h
    simp at *
    omega
  . rename_i h
    let so := List.sizeOf_lt_of_mem h
    simp at *
    omega


def List.sum [Add α] [OfNat α 0] (xs : List α) : α :=
  xs.foldl (· + ·) 0

-- A computable size of residuals, not including the size of types
def TypedExpr.size (r : TypedExpr) : Nat :=
 match r with
  | .lit _l _ty => 1
  | .var _v _ty => 1
  | .ite cond thenExpr elseExpr ty => 1 + TypedExpr.size cond + TypedExpr.size thenExpr + TypedExpr.size elseExpr
  | .and a b ty => 1 + TypedExpr.size a + TypedExpr.size b
  | .or a b ty => 1 + TypedExpr.size a + TypedExpr.size b
  | .unaryApp op expr ty => 1 + TypedExpr.size expr
  | .binaryApp op a b ty => 1 + TypedExpr.size a + TypedExpr.size b
  | .getAttr expr attr ty => 1 + TypedExpr.size expr
  | .hasAttr expr attr ty => 1 + TypedExpr.size expr
  | .set ls ty => (ls.map₁ (λ ⟨v, _⟩ => TypedExpr.size v)).sum + 1
  | .record map ty => (map.map₂ (λ ⟨⟨_attr, v⟩, _⟩ => TypedExpr.size v)).sum + 1
  | .call xfn args ty => (args.map₁ (λ ⟨v, _⟩ => TypedExpr.size v)).sum + 1
termination_by sizeOf r
decreasing_by
  repeat case _ =>
    simp [*]; try omega
  . rename_i h
    let so := List.sizeOf_lt_of_mem h
    simp
    omega
  . rename_i h
    simp at *
    omega
  . rename_i h
    let so := List.sizeOf_lt_of_mem h
    simp at *
    omega


/--
The batched evaluation loop
  1. Asks for any new entities referenced by the residual
  2. Partially evaluates now that new entities are loaded
  3. Continues if progress has been made, evaluating otherwise

The subtle part of this algorithm is why it can use the normal Cedar.Spec.evaluate when no progress is made.

When no progress is made, one of these cases must be true:
  - We have reduced the expression to a value
  - An entity or entity field is missing, so the expression will error
-/
def batchedEvalLoop
  (expr : TypedExpr)
  (req : Request)
  (loader : EntityLoader)
  (store : Entities)
  : Result Value :=
  let toLoad := (TypedExpr.allLiteralUIDs expr).filter (λ uid => (store.find? uid).isNone)
  let newEntities := loader toLoad
  let newStore := newEntities.kvs.foldl (λ acc ed => acc.insert ed.1 ed.2) store

  do
    let newRes := Cedar.TPE.evaluate expr (Request.asPartialRequest req) (Entities.asPartial newStore)
    let newExprRes ← newRes.asTypedExpr
    if TypedExpr.size newExprRes < TypedExpr.size expr
    then batchedEvalLoop newExprRes req loader newStore
    else Cedar.Spec.evaluate expr.toExpr req newStore

termination_by TypedExpr.size expr
decreasing_by
  simp [TypedExpr.size]
  omega


/--
Evaluate a cedar expression using an EntityLoader
instead of a full Entities store.
This algorithm minimizes the number of calls to the EntityLoader using partial evaluation.
-/
def batchedEvaluate
  (x : TypedExpr)
  (req : Request)
  (loader : EntityLoader)
  : Result Value :=
  let emptyStore : Entities := Map.mk []
  -- an initial partial evaluation, removing all variables
  let residual := Cedar.TPE.evaluate x (Request.asPartialRequest req) (Entities.asPartial emptyStore)
  -- start the batched evaluation loop
  do
    let newExpr ← residual.asTypedExpr
    batchedEvalLoop newExpr req loader emptyStore

def entityLoaderFor : (e: Entities) -> EntityLoader :=
  fun e =>
   fun uids =>
    Map.make (uids.toList.filterMap (fun uid =>
      e.find? uid |>.map (fun data => (uid, data))))
