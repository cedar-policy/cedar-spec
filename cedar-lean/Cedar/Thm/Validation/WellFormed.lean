import Cedar.Spec.Entities
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.Data

namespace Cedar.Validation
open Cedar.Spec

def lowerBound (ty : CedarType) : Level :=
  match ty with
  | .bool _
  | .int
  | .string
  | .ext _
  | .set _
    => .infinite
  | .entity _ l => l
  | .record members =>
    let levels := (List.map₁ members.kvs (λ prod => lowerBound prod.val.snd.getType) )
    List.foldr min .infinite levels
termination_by sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals try omega
  have h₁ : sizeOf prod.val < sizeOf members.kvs := by
    apply List.sizeOf_lt_of_mem
    exact prod.property
  have h₂ : sizeOf members.kvs < sizeOf members :=  by
    apply Cedar.Data.Map.sizeOf_lt_of_kvs
  have h₃ : sizeOf prod.val.snd.getType < sizeOf prod.val := by
    cases prod.val
    rename_i a b
    simp [Prod.snd, Qualified.getType]
    split <;> simp <;> omega
  omega

def InstanceOfBoolType : Bool → BoolType → Prop
  | true,  .tt      => True
  | false, .ff      => True
  | _,     .anyBool => True
  | _, _            => False

def InstanceOfEntityType (e : EntityUID) (ety: EntityType) : Prop :=
  ety = e.ty

def InstanceOfExtType : Ext → ExtType → Prop
  | .decimal _, .decimal => True
  | .ipaddr _,  .ipAddr  => True
  | _, _                 => False


end Cedar.Validation
