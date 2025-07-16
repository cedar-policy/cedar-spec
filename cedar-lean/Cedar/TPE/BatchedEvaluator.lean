import Cedar.Spec
import Cedar.Data
import Cedar.TPE.Residual
import Cedar.TPE.Evaluator
import Cedar.TPE.Input

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation


def EntityLoader: Type := (Set EntityUID) -> Map EntityUID EntityData

def find_next_batch (x : Residual) : Set EntityUID :=
  match x with
  | .val v ty =>
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
  | .ite c t e _ => find_next_batch c ∪ find_next_batch t ∪ find_next_batch e
  | .and a b _   => find_next_batch a ∪ find_next_batch b
  | .or a b _    => find_next_batch a ∪ find_next_batch b
  | .unaryApp _ e _ => find_next_batch e
  | .binaryApp _ a b _ => find_next_batch a ∪ find_next_batch b
  | .getAttr e _ _ => find_next_batch e
  | .hasAttr e _ _ => find_next_batch e
  | .set ls _ => ls.foldl (λ acc r => acc ∪ find_next_batch r) Set.empty
  | .record m _ => m.foldl (λ acc (_, r) => acc ∪ find_next_batch r) Set.empty
  | .call _ args _ => args.foldl (λ acc r => acc ∪ find_next_batch r) Set.empty
  | .error _ => Set.empty


-- A computable size of residuals, not including the size of types
def Residual.size (r: Residual): Nat :=
 match r with
  | .val v ty => 1
  | .var v ty => 1
  | .ite cond thenExpr elseExpr ty => 1 + Residual.size cond + Residual.size thenExpr + Residual.size elseExpr
  | .and a b ty => 1 + Residual.size a + Residual.size b
  | .or a b ty => 1 + Residual.size a + Residual.size b
  | .unaryApp op expr ty => 1 + Residual.size expr
  | .binaryApp op a b ty => 1 + Residual.size a + Residual.size b
  | .getAttr expr attr ty => 1 + Residual.size expr + Residual.size attr
  | .hasAttr expr attr ty => 1 + Residual.size expr + Residual.size attr
  | .set ls ty => ls.foldl (λ s r => s + r.size) 1
  | .record map ty => map.foldl (λ s kv => s + kv.2.size) 1
  | .call xfn args ty => args.foldl (λ s r => s + r.size) 1
  | .error ty => 1


def batched_eval_loop
  (res : Residual)
  (req: Request)
  (loader: EntityLoader)
  (store: Entities)
  : Result Value :=
  let to_load := (find_next_batch res).filter (λ uid => (store.find? uid).isNone)
  let new_entities := loader to_load
  let new_store := new_entities.kvs.foldl (λ acc ed => acc.insert ed.1 ed.2) store

  do
    let expr ← res.asTypedExpr
    let new_res := Cedar.TPE.evaluate expr (Request.asPartialRequest req) (Entities.asPartial new_store)
    match new_res.asValue with
    | some v => .ok v
    | none =>
      if new_res.size < res.size
      then batched_eval_loop new_res req loader new_store
      else Cedar.Spec.evaluate expr.toExpr req new_store

def batched_evaluate
  (x : TypedExpr)
  (req: Request)/-  -/
  (loader: EntityLoader)
  : Result Value
  :=
  let empty_store : Entities := Map.mk []
  -- do a first partial evaluation on x
  let residual := Cedar.TPE.evaluate x (Request.asPartialRequest req) (Entities.asPartial empty_store)
  -- start the batching loop
  batched_eval_loop residual req loader empty_store
