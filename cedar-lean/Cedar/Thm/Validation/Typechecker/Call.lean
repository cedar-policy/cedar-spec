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

import Cedar.Thm.Validation.Typechecker.Basic

/-!
This file proves that typechecking of `.call` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_call_decimal_inversion {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.call .decimal xs) c env = Except.ok (ty, c')) :
  ty = .ext .decimal ∧
  c' = ∅ ∧
  ∃ (s : String),
    xs = [.lit (.string s)] ∧
    (Cedar.Spec.Ext.Decimal.decimal s).isSome
:= by
  simp [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp [h₂] at h₁
  rename_i tys
  simp [typeOfCall, typeOfConstructor] at h₁
  split at h₁ <;> simp [ok, err] at h₁
  rename_i s
  split at h₁ <;> simp at h₁
  simp [h₁]
  rename_i h₃
  simp [h₃]

theorem type_of_call_decimal_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : typeOf (Expr.call .decimal xs) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.call .decimal xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .decimal xs) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨h₂, h₃, s, h₄, h₅⟩ := type_of_call_decimal_inversion h₁
  subst h₂ h₃ h₄
  apply And.intro empty_guarded_capabilities_invariant
  rw [Option.isSome_iff_exists] at h₅
  have ⟨d, h₅⟩ := h₅
  exists .ext d
  constructor
  · simp [EvaluatesTo, evaluate, List.mapM₁, List.mapM, List.mapM.loop, call, res, h₅, Coe.coe]
  · apply InstanceOfType.instance_of_ext
    simp [InstanceOfExtType]

theorem type_of_call_ip_inversion {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.call .ip xs) c env = Except.ok (ty, c')) :
  ty = .ext .ipAddr ∧
  c' = ∅ ∧
  ∃ (s : String),
    xs = [.lit (.string s)] ∧
    (Cedar.Spec.Ext.IPAddr.ip s).isSome
:= by
  simp [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp [h₂] at h₁
  rename_i tys
  simp [typeOfCall, typeOfConstructor] at h₁
  split at h₁ <;> simp [ok, err] at h₁
  rename_i s
  split at h₁ <;> simp at h₁
  simp [h₁]
  rename_i h₃
  simp [h₃]

theorem type_of_call_ip_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : typeOf (Expr.call .ip xs) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.call .ip xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .ip xs) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨h₂, h₃, s, h₄, h₅⟩ := type_of_call_ip_inversion h₁
  subst h₂ h₃ h₄
  apply And.intro empty_guarded_capabilities_invariant
  rw [Option.isSome_iff_exists] at h₅
  have ⟨ip, h₅⟩ := h₅
  exists .ext ip
  constructor
  · simp [EvaluatesTo, evaluate, List.mapM₁, List.mapM, List.mapM.loop, call, res, h₅, Coe.coe]
  · apply InstanceOfType.instance_of_ext
    simp [InstanceOfExtType]

theorem typeOf_of_binary_call_inversion {xs : List Expr} {c : Capabilities} {env : Environment} {ty₁ ty₂ : CedarType}
  (h₁ : (xs.mapM₁ fun x => justType (typeOf x.val c env)) = Except.ok [ty₁, ty₂]) :
  ∃ x₁ x₂ c₁ c₂,
    xs = [x₁, x₂] ∧
    typeOf x₁ c env = ok ty₁ c₁ ∧
    typeOf x₂ c env = ok ty₂ c₂
:= by
  simp [List.mapM₁] at h₁
  cases xs
  case nil =>
    simp [List.mapM, List.mapM.loop, pure, Except.pure] at h₁
  case cons hd₁ tl₁ =>
    cases tl₁
    case nil =>
      simp [List.mapM, List.mapM.loop] at h₁
      cases h₂ : justType (typeOf hd₁ c env) <;>
      simp [h₂] at h₁
      simp [pure, Except.pure] at h₁
    case cons hd₂ tl₂ =>
      cases tl₂
      case nil =>
        rw [List.attach, List.pmap, List.mapM, List.mapM.loop, justType, Except.map] at h₁
        split at h₁ <;> simp at h₁
        rw [List.mapM.loop, justType, Except.map] at h₁
        split at h₁ <;> simp at h₁
        simp [List.mapM.loop, pure, Except.pure] at h₁
        rename_i res₁ h₂ _ res₂ h₃
        exists hd₁, hd₂, res₁.2, res₂.2
        simp [ok]
        have ⟨hl₁, hr₁⟩ := h₁
        subst hl₁ hr₁
        simp at h₂ h₃
        simp [h₂, h₃]
      case cons hd₃ tl₃ =>
        simp [List.attach] at h₁
        simp [List.mapM_pmap_subtype (fun x => justType (typeOf x c env))] at h₁
        rw [justType, Except.map] at h₁
        split at h₁ <;> simp at h₁
        rw [justType, Except.map] at h₁
        split at h₁ <;> simp at h₁
        rw [justType, Except.map] at h₁
        split at h₁ <;> simp at h₁
        rename_i res₁ _ _ res₂ _ _ res₃ _
        simp [pure, Except.pure] at h₁
        cases h₂ : List.mapM (fun x => justType (typeOf x c env)) tl₃ <;> simp [h₂] at h₁

def IsDecimalComparator : ExtFun → Prop
  | .lessThan
  | .lessThanOrEqual
  | .greaterThan
  | .greaterThanOrEqual => True
  | _                   => False

theorem type_of_call_decimal_comparator_inversion {xfn : ExtFun} {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType}
  (h₀ : IsDecimalComparator xfn)
  (h₁ : typeOf (Expr.call xfn xs) c env = Except.ok (ty, c')) :
  ty = .bool .anyBool ∧
  c' = ∅ ∧
  ∃ (x₁ x₂ : Expr) (c₁ c₂ : Capabilities),
    xs = [x₁, x₂] ∧
    typeOf x₁ c env = ok (.ext .decimal) c₁ ∧
    typeOf x₂ c env = ok (.ext .decimal) c₂
:= by
  simp [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp [h₂] at h₁
  rename_i tys
  simp [typeOfCall] at h₁
  simp [IsDecimalComparator] at h₀
  split at h₀
  all_goals {
    split at h₁ <;> try { contradiction }
    all_goals {
      simp [ok] at h₁
      simp only [h₁, List.empty_eq, true_and]
      apply typeOf_of_binary_call_inversion h₂
    }
  }

theorem type_of_call_decimal_comparator_is_sound {xfn : ExtFun} {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₀ : IsDecimalComparator xfn)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.call xfn xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call xfn xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call xfn xs) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨h₄, h₅, x₁, x₂, c₁', c₂', h₆, h₇, h₈⟩ := type_of_call_decimal_comparator_inversion h₀ h₃
  subst h₄ h₅ h₆
  apply And.intro empty_guarded_capabilities_invariant
  simp [EvaluatesTo, evaluate, List.mapM₁, List.attach]
  have ih₁ := ih x₁
  have ih₂ := ih x₂
  simp [TypeOfIsSound] at ih₁ ih₂
  have ⟨_, v₁, hl₁, hr₁⟩ := ih₁ h₁ h₂ h₇
  have ⟨_, v₂, hl₂, hr₂⟩ := ih₂ h₁ h₂ h₈
  simp [EvaluatesTo] at hl₁
  rcases hl₁ with hl₁ | hl₁ | hl₁ | hl₁ <;>
  simp [hl₁] <;>
  try { exact type_is_inhabited (CedarType.bool BoolType.anyBool)}
  rcases hl₂ with hl₂ | hl₂ | hl₂ | hl₂ <;>
  simp [hl₂] <;>
  try { exact type_is_inhabited (CedarType.bool BoolType.anyBool)}
  have ⟨d₁, hr₁⟩ := instance_of_decimal_type_is_decimal hr₁
  have ⟨d₂, hr₂⟩ := instance_of_decimal_type_is_decimal hr₂
  subst hr₁ hr₂
  simp [IsDecimalComparator] at h₀
  split at h₀ <;>
  simp [call] <;> try { contradiction }
  all_goals {
    apply bool_is_instance_of_anyBool
  }

theorem type_of_call_isInRange_inversion {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.call .isInRange xs) c env = Except.ok (ty, c')) :
  ty = .bool .anyBool ∧
  c' = ∅ ∧
  ∃ (x₁ x₂ : Expr) (c₁ c₂ : Capabilities),
    xs = [x₁, x₂] ∧
    typeOf x₁ c env = ok (.ext .ipAddr) c₁ ∧
    typeOf x₂ c env = ok (.ext .ipAddr) c₂
:= by
  simp [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp [h₂] at h₁
  rename_i tys
  simp [typeOfCall] at h₁
  split at h₁ <;> try { contradiction }
  all_goals {
    simp [ok] at h₁
    simp only [h₁, List.empty_eq, true_and]
    apply typeOf_of_binary_call_inversion h₂
  }

theorem type_of_call_isInRange_comparator_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.call .isInRange xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call .isInRange xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .isInRange xs) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨h₄, h₅, x₁, x₂, c₁', c₂', h₆, h₇, h₈⟩ := type_of_call_isInRange_inversion h₃
  subst h₄ h₅ h₆
  apply And.intro empty_guarded_capabilities_invariant
  simp [EvaluatesTo, evaluate, List.mapM₁, List.attach]
  have ih₁ := ih x₁
  have ih₂ := ih x₂
  simp [TypeOfIsSound] at ih₁ ih₂
  have ⟨_, v₁, hl₁, hr₁⟩ := ih₁ h₁ h₂ h₇
  have ⟨_, v₂, hl₂, hr₂⟩ := ih₂ h₁ h₂ h₈
  simp [EvaluatesTo] at hl₁
  rcases hl₁ with hl₁ | hl₁ | hl₁ | hl₁ <;>
  simp [hl₁] <;>
  try { exact type_is_inhabited (CedarType.bool BoolType.anyBool)}
  rcases hl₂ with hl₂ | hl₂ | hl₂ | hl₂ <;>
  simp [hl₂] <;>
  try { exact type_is_inhabited (CedarType.bool BoolType.anyBool)}
  have ⟨d₁, hr₁⟩ := instance_of_ipAddr_type_is_ipAddr hr₁
  have ⟨d₂, hr₂⟩ := instance_of_ipAddr_type_is_ipAddr hr₂
  subst hr₁ hr₂
  simp [call]
  apply bool_is_instance_of_anyBool

def IsIpAddrRecognizer : ExtFun → Prop
  | .isIpv4
  | .isIpv6
  | .isLoopback
  | .isMulticast => True
  | _            => False


theorem typeOf_of_unary_call_inversion {xs : List Expr} {c : Capabilities} {env : Environment} {ty₁ : CedarType}
  (h₁ : (xs.mapM₁ fun x => justType (typeOf x.val c env)) = Except.ok [ty₁]) :
  ∃ x₁ c₁,
    xs = [x₁] ∧
    typeOf x₁ c env = ok ty₁ c₁
:= by
  simp [List.mapM₁] at h₁
  cases xs
  case nil =>
    simp [List.mapM, List.mapM.loop, pure, Except.pure] at h₁
  case cons hd₁ tl₁ =>
    cases tl₁
    case nil =>
      simp [List.mapM, List.mapM.loop] at h₁
      cases h₂ : justType (typeOf hd₁ c env) <;>
      simp [h₂] at h₁
      simp [justType, Except.map] at h₂
      simp [pure, Except.pure] at h₁
      subst h₁
      split at h₂ <;> simp at h₂
      rename_i res₁ h₃
      exists hd₁, res₁.snd
      simp [ok, h₃, ←h₂]
    case cons hd₂ tl₂ =>
      simp [List.attach] at h₁
      simp [List.mapM_pmap_subtype (fun x => justType (typeOf x c env))] at h₁
      rw [justType, Except.map] at h₁
      split at h₁ <;> simp at h₁
      rw [justType, Except.map] at h₁
      split at h₁ <;> simp at h₁
      rename_i res₁ _ _ res₂ _
      simp [pure, Except.pure] at h₁
      cases h₂ : List.mapM (fun x => justType (typeOf x c env)) tl₂ <;> simp [h₂] at h₁

theorem type_of_call_ipAddr_recognizer_inversion {xfn : ExtFun} {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType}
  (h₀ : IsIpAddrRecognizer xfn)
  (h₁ : typeOf (Expr.call xfn xs) c env = Except.ok (ty, c')) :
  ty = .bool .anyBool ∧
  c' = ∅ ∧
  ∃ (x₁ : Expr) (c₁ : Capabilities),
    xs = [x₁] ∧
    typeOf x₁ c env = ok (.ext .ipAddr) c₁
:= by
  simp [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp [h₂] at h₁
  rename_i tys
  simp [typeOfCall] at h₁
  simp [IsIpAddrRecognizer] at h₀
  split at h₀
  all_goals {
    split at h₁ <;> try { contradiction }
    all_goals {
      simp [ok] at h₁
      simp only [h₁, List.empty_eq, true_and]
      apply typeOf_of_unary_call_inversion h₂
    }
  }

theorem type_of_call_ipAddr_recognizer_is_sound {xfn : ExtFun} {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₀ : IsIpAddrRecognizer xfn)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.call xfn xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call xfn xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call xfn xs) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨h₄, h₅, x₁, c₁', h₆, h₇⟩ := type_of_call_ipAddr_recognizer_inversion h₀ h₃
  subst h₄ h₅ h₆
  apply And.intro exact empty_guarded_capabilities_invariant
  simp [EvaluatesTo, evaluate, List.mapM₁, List.attach]
  have ih₁ := ih x₁
  simp [TypeOfIsSound] at ih₁
  have ⟨_, v₁, hl₁, hr₁⟩ := ih₁ h₁ h₂ h₇
  simp [EvaluatesTo] at hl₁
  rcases hl₁ with hl₁ | hl₁ | hl₁ | hl₁ <;>
  simp [hl₁] <;>
  try { exact type_is_inhabited (CedarType.bool BoolType.anyBool)}
  have ⟨ip₁, hr₁⟩ := instance_of_ipAddr_type_is_ipAddr hr₁
  subst hr₁
  simp [IsIpAddrRecognizer] at h₀
  split at h₀ <;>
  simp [call] <;> try { contradiction }
  all_goals {
    apply bool_is_instance_of_anyBool
  }

theorem type_of_call_is_sound {xfn : ExtFun} {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.call xfn xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call xfn xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call xfn xs) request entities v ∧ InstanceOfType v ty
:= by
  match xfn with
  | .decimal            => exact type_of_call_decimal_is_sound h₃
  | .ip                 => exact type_of_call_ip_is_sound h₃
  | .lessThan
  | .lessThanOrEqual
  | .greaterThan
  | .greaterThanOrEqual => exact type_of_call_decimal_comparator_is_sound (by simp [IsDecimalComparator]) h₁ h₂ h₃ ih
  | .isInRange          => exact type_of_call_isInRange_comparator_is_sound h₁ h₂ h₃ ih
  | .isIpv4
  | .isIpv6
  | .isLoopback
  | .isMulticast        => exact type_of_call_ipAddr_recognizer_is_sound (by simp [IsIpAddrRecognizer]) h₁ h₂ h₃ ih

end Cedar.Thm
