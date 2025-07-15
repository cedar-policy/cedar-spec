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

def batched_eval_loop
  (res : Residual)
  (req: Request)
  (loader: EntityLoader)
  (store: PartialEntities)
  : Result Value :=
  let to_load := (find_next_batch x).filter (λ uid => (store.get uid PartialEntityData.attrs).isNone)
  let new_entities := loader to_load
  let new_store := new_entities.kvs.foldl (λ acc ed => acc.insert ed.1 (EntityData.asPartialEntityData ed.2)) store

  let new_res := Cedar.TPE.evaluate res (Request.asPartialRequest req) new_store

  sorry

def batched_evaluate
  (x : TypedExpr)
  (req: Request)/-  -/
  (loader: EntityLoader)
  : Result Value
  :=
  let empty_store : PartialEntities := Map.mk []
  -- do a first partial evaluation on x
  let residual := Cedar.TPE.evaluate x (Request.asPartialRequest req) empty_store
  -- start the batching loop
  batched_eval_loop residual req loader empty_store
