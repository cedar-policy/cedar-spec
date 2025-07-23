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

def EntityLoader : Type := Set EntityUID → Map EntityUID PartialEntityData

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
partial def batchedEvalLoop
  (expr : TypedExpr)
  (req : Request)
  (loader : EntityLoader)
  (store : PartialEntities)
  : Result Value :=
  let toLoad := (TypedExpr.allLiteralUIDs expr).filter (λ uid => (store.find? uid).isNone)
  let newEntities := loader toLoad
  let newStore := newEntities.kvs.foldl (λ acc ed => acc.insert ed.1 ed.2) store
  let newRes := Cedar.TPE.evaluate expr (Request.asPartialRequest req) newStore

  match newRes with
  | .val v _ty => .ok v
  | _ =>
    do
      let newExprRes ← newRes.asTypedExpr
      batchedEvalLoop newExprRes req loader newStore


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
  let emptyStore : PartialEntities := Map.mk []
  -- an initial partial evaluation, removing all variables
  let residual := Cedar.TPE.evaluate x (Request.asPartialRequest req) emptyStore
  -- start the batched evaluation loop
  do
    let newExpr ← residual.asTypedExpr
    batchedEvalLoop newExpr req loader emptyStore

def entityLoaderFor : (e: Entities) -> EntityLoader :=
  fun e =>
   fun uids =>
    Map.make (uids.toList.map (fun uid =>
      match (e.find? uid) with
      | .some data =>
        (uid, EntityData.asPartial data)
      | .none =>
        (uid, PartialEntityData.MissingEntity)))
