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
 Possible improvments
 - Some entities don't need to be loaded at all (User::"oliver" == User::"emina")
 - Never load ancestors- instead, ask if something is an ancestor of something else
  - Configurable: Fewer pulls if you load all ancestors
 - Analysis for how many calls to the entity loader there will be
-/

def EntityLoader: Type := (Set EntityUID) -> Map EntityUID EntityData

def findNextBatch (x : Residual) : Set EntityUID :=
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
  | .ite c t e _ => findNextBatch c ∪ findNextBatch t ∪ findNextBatch e
  | .and a b _   => findNextBatch a ∪ findNextBatch b
  | .or a b _    => findNextBatch a ∪ findNextBatch b
  | .unaryApp _ e _ => findNextBatch e
  | .binaryApp _ a b _ => findNextBatch a ∪ findNextBatch b
  | .getAttr e _ _ => findNextBatch e
  | .hasAttr e _ _ => findNextBatch e
  | .set ls _ => ls.mapUnion₁ (λ ⟨v, _⟩ => findNextBatch v)
  | .record m _ => m.mapUnion₂ (λ ⟨⟨_attr, v⟩, _⟩ => findNextBatch v)
  | .call _ ls _ => ls.mapUnion₁ (λ ⟨v, _⟩ => findNextBatch v)
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
    simp
    simp at h
    omega
  . rename_i h
    simp
    let so := List.sizeOf_lt_of_mem h
    simp at so
    omega


def List.sum [Add α] [OfNat α 0] (xs : List α) : α :=
  xs.foldl (· + ·) 0

-- A computable size of residuals, not including the size of types
def Residual.size (r: Residual): Nat :=
 match r with
  | .val _v _ty => 1
  | .var _v _ty => 1
  | .ite cond thenExpr elseExpr ty => 1 + Residual.size cond + Residual.size thenExpr + Residual.size elseExpr
  | .and a b ty => 1 + Residual.size a + Residual.size b
  | .or a b ty => 1 + Residual.size a + Residual.size b
  | .unaryApp op expr ty => 1 + Residual.size expr
  | .binaryApp op a b ty => 1 + Residual.size a + Residual.size b
  | .getAttr expr attr ty => 1 + Residual.size expr
  | .hasAttr expr attr ty => 1 + Residual.size expr
  | .set ls ty => (ls.map₁ (λ ⟨v, _⟩ => v.size)).sum + 1
  | .record map ty => (map.map₂ (λ ⟨⟨_attr, v⟩, _⟩ => v.size)).sum + 1
  | .call xfn args ty => (args.map₁ (λ ⟨v, _⟩ => v.size)).sum +  1
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
    simp
    simp at h
    omega
  . rename_i h
    simp
    let so := List.sizeOf_lt_of_mem h
    simp at so
    omega


/--
The batched evaluation loop
  1. Asks for any new entities referenced by the residual
  2. Partially evaluates now that new entities are loaded
  3. Continues if progress has been made, evaluating otherwise

The subtle part of this algorithm is why it can use the normal Cedar.Spec.evaluate when no progress is made.
The argument is that if no progress is made during partial
evaluation, there must be a missing field or entity causing
the algorithm to get stuck.
-/
def batched_eval_loop
  (res : Residual)
  (req: Request)
  (loader: EntityLoader)
  (store: Entities)
  : Result Value :=
  let to_load := (findNextBatch res).filter (λ uid => (store.find? uid).isNone)
  let new_entities := loader to_load
  let new_store := new_entities.kvs.foldl (λ acc ed => acc.insert ed.1 ed.2) store

  do
    let expr ← res.asTypedExpr
    let new_res := Cedar.TPE.evaluate expr (Request.asPartialRequest req) (Entities.asPartial new_store)
    if new_res.size < res.size
    then batched_eval_loop new_res req loader new_store
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
  (req: Request)/-  -/
  (loader: EntityLoader)
  : Result Value
  :=
  let empty_store : Entities := Map.mk []
  -- an initial partial evaluation, removing all variables
  let residual := Cedar.TPE.evaluate x (Request.asPartialRequest req) (Entities.asPartial empty_store)
  -- start the batched evaluation loop
  batched_eval_loop residual req loader empty_store
