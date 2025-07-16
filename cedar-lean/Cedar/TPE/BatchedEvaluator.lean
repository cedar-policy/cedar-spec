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

def Residual.allLiteralUIDs (x : Residual) : Set EntityUID :=
  match x with
  | .val v _ty =>
    match v with
    | .prim (.entityUID uid) => Set.singleton uid
    | _ => Set.empty
  | .var v _ =>
    -- these cases should not happen, since the request was fully concrete
    match v with
    | .principal => Set.empty
    | .resource  => Set.empty
    | .action    => Set.empty
    | .context   => Set.empty
  | .ite c t e _ => c.allLiteralUIDs ∪ t.allLiteralUIDs ∪ e.allLiteralUIDs
  | .and a b _   => a.allLiteralUIDs ∪ b.allLiteralUIDs
  | .or a b _    => a.allLiteralUIDs ∪ b.allLiteralUIDs
  | .unaryApp _ e _ => e.allLiteralUIDs
  | .binaryApp _ a b _ => a.allLiteralUIDs ∪ b.allLiteralUIDs
  | .getAttr e _ _ => e.allLiteralUIDs
  | .hasAttr e _ _ => e.allLiteralUIDs
  | .set ls _ => ls.mapUnion₁ (λ ⟨v, _⟩ => v.allLiteralUIDs)
  | .record m _ => m.mapUnion₂ (λ ⟨⟨_attr, v⟩, _⟩ => v.allLiteralUIDs)
  | .call _ ls _ => ls.mapUnion₁ (λ ⟨v, _⟩ => v.allLiteralUIDs)
  | .error _ => Set.empty
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
def Residual.size (r : Residual) : Nat :=
 match r with
  | .val _v _ty => 1
  | .var _v _ty => 1
  | .ite cond thenExpr elseExpr ty => 1 + cond.size + thenExpr.size + elseExpr.size
  | .and a b ty => 1 + a.size + b.size
  | .or a b ty => 1 + a.size + b.size
  | .unaryApp op expr ty => 1 + expr.size
  | .binaryApp op a b ty => 1 + a.size + b.size
  | .getAttr expr attr ty => 1 + expr.size
  | .hasAttr expr attr ty => 1 + expr.size
  | .set ls ty => (ls.map₁ (λ ⟨v, _⟩ => v.size)).sum + 1
  | .record map ty => (map.map₂ (λ ⟨⟨_attr, v⟩, _⟩ => v.size)).sum + 1
  | .call xfn args ty => (args.map₁ (λ ⟨v, _⟩ => v.size)).sum + 1
  | .error _ty => 1
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
  (res : Residual)
  (req : Request)
  (loader : EntityLoader)
  (store : Entities)
  : Result Value :=
  let to_load := res.allLiteralUIDs.filter (λ uid => (store.find? uid).isNone)
  let new_entities := loader to_load
  let new_store := new_entities.kvs.foldl (λ acc ed => acc.insert ed.1 ed.2) store

  do
    let expr ← res.asTypedExpr
    let new_res := Cedar.TPE.evaluate expr (Request.asPartialRequest req) (Entities.asPartial new_store)
    if new_res.size < res.size
    then batchedEvalLoop new_res req loader new_store
    else Cedar.Spec.evaluate expr.toExpr req new_store

termination_by res.size
decreasing_by
  rename_i h
  subst new_res
  subst new_store
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
  let empty_store : Entities := Map.mk []
  -- an initial partial evaluation, removing all variables
  let residual := Cedar.TPE.evaluate x (Request.asPartialRequest req) (Entities.asPartial empty_store)
  -- start the batched evaluation loop
  batchedEvalLoop residual req loader empty_store
