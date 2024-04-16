/-
 Copyright Cedar Contributors

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

import Cedar.Thm.Data.LT
import Cedar.Thm.Validation.Typechecker.Basic

/-!
This file proves that typechecking of `.record` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

def AttrValueHasAttrType (av : Attr × Value) (aqty : Attr × QualifiedType) : Prop :=
  av.fst = aqty.fst ∧ InstanceOfType av.snd (Qualified.getType aqty.snd)

def AttrExprHasAttrType (c : Capabilities) (env : Environment) (ax : Attr × Expr) (aqty : Attr × QualifiedType) : Prop :=
  ∃ ty' c',
    aqty = (ax.fst, .required ty') ∧
    typeOf ax.snd c env = Except.ok (ty', c')

theorem type_of_record_inversion_forall {axs : List (Attr × Expr)} {c : Capabilities} {env : Environment} {rty : List (Attr × QualifiedType)}
  (h₁ : List.mapM (fun x => requiredAttr x.fst (typeOf x.snd c env)) axs = Except.ok rty) :
  List.Forall₂ (AttrExprHasAttrType c env) axs rty
:= by
  cases axs
  case nil =>
    simp [pure, Except.pure] at h₁ ; subst h₁ ; apply List.Forall₂.nil
  case cons hd tl =>
    cases rty
    case nil =>
      simp [←List.mapM'_eq_mapM] at h₁
      cases h₂ : requiredAttr hd.fst (typeOf hd.snd c env) <;> simp [h₂] at h₁
      cases h₃ : List.mapM' (fun x => requiredAttr x.fst (typeOf x.snd c env)) tl <;> simp [h₃] at h₁
      simp [pure, Except.pure] at h₁
    case cons hd' tl' =>
      apply List.Forall₂.cons
      {
        simp [←List.mapM'_eq_mapM] at h₁
        cases h₂ : requiredAttr hd.fst (typeOf hd.snd c env) <;> simp [h₂] at h₁
        cases h₃ : List.mapM' (fun x => requiredAttr x.fst (typeOf x.snd c env)) tl <;> simp [h₃] at h₁
        simp [pure, Except.pure] at h₁
        have ⟨hl₁, hr₁⟩ := h₁
        rw [eq_comm] at hl₁ hr₁ ; subst hl₁ hr₁
        simp [requiredAttr, Except.map] at h₂
        split at h₂ <;> simp at h₂
        subst h₂
        rename_i _ r _
        simp [AttrExprHasAttrType]
        exists r.snd
      }
      {
        apply type_of_record_inversion_forall
        simp [←List.mapM'_eq_mapM] at *
        cases h₂ : requiredAttr hd.fst (typeOf hd.snd c env) <;> simp [h₂] at h₁
        cases h₃ : List.mapM' (fun x => requiredAttr x.fst (typeOf x.snd c env)) tl <;> simp [h₃] at h₁
        simp [pure, Except.pure] at h₁
        simp [h₁]
      }

theorem type_of_record_inversion {axs : List (Attr × Expr)} {c c' : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.record axs) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  ∃ (rty : List (Attr × QualifiedType)),
    ty = .record (Map.make rty) ∧
    List.Forall₂ (AttrExprHasAttrType c env) axs rty
:= by
  simp [typeOf, ok] at h₁
  cases h₂ : List.mapM₂ axs fun x => requiredAttr x.1.fst (typeOf x.1.snd c env) <;> simp [h₂] at h₁
  rename_i rty
  simp [h₁]
  exists rty ; simp [h₁]
  simp [List.mapM₂, List.attach₂] at h₂
  simp [List.mapM_pmap_subtype (fun (x : Attr × Expr) => requiredAttr x.fst (typeOf x.snd c env))] at h₂
  exact type_of_record_inversion_forall h₂

theorem mk_vals_instance_of_mk_types₁ {a : Attr} {avs : List (Attr × Value)} {rty : List (Attr × QualifiedType)}
  (h₁ : List.Forall₂ AttrValueHasAttrType avs rty)
  (h₂ : Map.contains (Map.mk avs) a = true) :
  Map.contains (Map.mk rty) a = true
:= by
  cases avs <;> cases rty <;> cases h₁
  case nil =>
    simp [Map.contains, Map.find?, List.find?] at h₂
  case cons ahd atl rhd rtl h₃ h₄ =>
    simp [Map.contains, Map.find?, List.find?] at *
    simp [AttrValueHasAttrType] at h₃
    have ⟨h₃, _⟩ := h₃ ; simp [h₃] at *
    cases h₅ : rhd.fst == a <;> simp [h₅] at *
    cases h₆ : List.find? (fun x => x.fst == a) atl <;> simp [h₆] at h₂
    have h₇ := @mk_vals_instance_of_mk_types₁ a atl rtl h₄
    simp [Map.contains, Map.find?, Map.kvs, h₆] at h₇
    exact h₇

theorem mk_vals_instance_of_mk_types₂ {a : Attr} {v : Value} {qty : QualifiedType} {avs : List (Attr × Value)} {rty : List (Attr × QualifiedType)}
  (h₁ : List.Forall₂ AttrValueHasAttrType avs rty)
  (h₂ : Map.find? (Map.mk avs) a = some v)
  (h₃ : Map.find? (Map.mk rty) a = some qty) :
  InstanceOfType v (Qualified.getType qty)
:= by
  cases avs <;> cases rty <;> cases h₁
  case nil =>
    simp [Map.find?, List.find?] at h₂
  case cons ahd atl rhd rtl h₄ h₅ =>
    simp [Map.find?, List.find?] at h₂ h₃
    simp [AttrValueHasAttrType] at h₄
    have ⟨hl₄, hr₄⟩ := h₄ ; simp [hl₄] at *
    cases h₆ : rhd.fst == a <;> simp [h₆] at h₂ h₃
    case true =>
      subst h₂ h₃
      exact hr₄
    case false =>
      apply @mk_vals_instance_of_mk_types₂ a v qty atl rtl h₅ <;>
      simp [Map.find?, Map.kvs, h₂, h₃]

theorem mk_vals_instance_of_mk_types₃ {a : Attr} {qty : QualifiedType} {avs : List (Attr × Value)} {rty : List (Attr × QualifiedType)}
  (h₁ : List.Forall₂ AttrValueHasAttrType avs rty)
  (h₂ : Map.find? (Map.mk rty) a = some qty)  :
  Map.contains (Map.mk avs) a = true
:= by
  cases avs <;> cases rty <;> cases h₁
  case nil =>
    simp [Map.find?, List.find?] at h₂
  case cons ahd atl rhd rtl h₄ h₅ =>
    simp [Map.contains, Map.find?, List.find?]
    simp [Map.find?, List.find?] at h₂
    simp [AttrValueHasAttrType] at h₄
    have ⟨h₄, _⟩ := h₄ ; simp [h₄] at *
    cases h₆ : rhd.fst == a <;> simp [h₆] at *
    cases h₇ : List.find? (fun x => x.fst == a) rtl <;> simp [h₇] at h₂
    have h₈ := @mk_vals_instance_of_mk_types₃ a qty atl rtl h₅
    simp [Map.find?, List.find?, Map.kvs, h₇, h₂, Map.contains] at h₈
    exact h₈

theorem mk_vals_instance_of_mk_types {avs : List (Attr × Value)} {rty : List (Attr × QualifiedType)}
  (h₁ : List.Forall₂ AttrValueHasAttrType avs rty) :
  InstanceOfType (Value.record (Map.mk avs)) (CedarType.record (Map.mk rty))
:= by
  apply InstanceOfType.instance_of_record
  case h₁ =>
    intro a h₂
    exact mk_vals_instance_of_mk_types₁ h₁ h₂
  case h₂ =>
    intro a v qty h₂ h₃
    exact mk_vals_instance_of_mk_types₂ h₁ h₂ h₃
  case h₃ =>
    intro a qty h₂ _
    exact mk_vals_instance_of_mk_types₃ h₁ h₂

theorem head_of_vals_instance_of_head_of_types {xhd : Attr × Expr} {c₁ : Capabilities} {env : Environment} {request : Request} {entities : Entities} {rhd : Attr × QualifiedType} {vhd : Attr × Value}
  (h₁ : TypeOfIsSound xhd.snd)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₄ : AttrExprHasAttrType c₁ env xhd rhd)
  (h₅ : bindAttr xhd.fst (evaluate xhd.snd request entities) = Except.ok vhd) :
  AttrValueHasAttrType vhd rhd
:= by
  simp [TypeOfIsSound] at h₁
  have ⟨ty', c', h₄, h₆⟩ := h₄ ; subst h₄
  specialize h₁ h₂ h₃ h₆
  have ⟨_, v, h₁, h₇⟩ := h₁
  simp [bindAttr] at h₅
  cases h₈ : evaluate xhd.snd request entities <;> simp [h₈] at h₅
  simp [EvaluatesTo, h₈] at h₁ ; subst h₁ h₅
  simp [AttrValueHasAttrType, Qualified.getType, h₇]

theorem vals_instance_of_types {axs : List (Attr × Expr)} {c₁ : Capabilities} {env : Environment} {request : Request} {entities : Entities} {rty : List (Attr × QualifiedType)} {avs : List (Attr × Value)}
  (ih : ∀ (axᵢ : Attr × Expr), axᵢ ∈ axs → TypeOfIsSound axᵢ.snd)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : List.Forall₂ (AttrExprHasAttrType c₁ env) axs rty)
  (h₄ : (axs.mapM fun x => bindAttr x.fst (evaluate x.snd request entities)) = Except.ok avs) :
  List.Forall₂ AttrValueHasAttrType avs rty
:= by
  cases h₃
  case nil =>
    simp [←List.mapM'_eq_mapM, pure, Except.pure] at h₄
    subst h₄
    simp only [List.Forall₂.nil]
  case cons xhd rhd xtl rtl h₅ h₆ =>
    simp [List.mapM'_eq_mapM, pure, Except.pure] at h₄
    cases h₇ : bindAttr xhd.fst (evaluate xhd.snd request entities) <;> simp [h₇] at h₄
    cases h₈ : List.mapM (fun x => bindAttr x.fst (evaluate x.snd request entities)) xtl <;> simp [h₈] at h₄
    subst h₄
    rename_i vhd vtl
    apply List.Forall₂.cons
    {
      apply head_of_vals_instance_of_head_of_types _ h₁ h₂ h₅ h₇
      apply ih ; simp only [List.mem_cons, true_or]
    }
    {
      apply @vals_instance_of_types xtl c₁ env request entities rtl vtl _ h₁ h₂ h₆ h₈
      intro ax h₉ ; apply ih ; simp [h₉]
    }

theorem type_of_record_is_sound_ok {axs : List (Attr × Expr)} {c₁ : Capabilities} {env : Environment} {request : Request} {entities : Entities} {rty : List (Attr × QualifiedType)} {avs : List (Attr × Value)}
  (ih : ∀ (axᵢ : Attr × Expr), axᵢ ∈ axs → TypeOfIsSound axᵢ.snd)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : List.Forall₂ (AttrExprHasAttrType c₁ env) axs rty)
  (h₄ : (axs.mapM fun x => bindAttr x.fst (evaluate x.snd request entities)) = Except.ok avs) :
  InstanceOfType (Value.record (Map.make avs)) (CedarType.record (Map.make rty))
:= by
  apply mk_vals_instance_of_mk_types
  let p := fun (v : Value) (qty : QualifiedType) => InstanceOfType v qty.getType
  have h₅ := vals_instance_of_types ih h₁ h₂ h₃ h₄
  have h₆ := List.canonicalize_preserves_forallᵥ p avs rty
  simp [List.Forallᵥ] at h₆
  exact h₆ h₅

theorem type_of_record_is_sound_err {axs : List (Attr × Expr)} {c₁ : Capabilities} {env : Environment} {request : Request} {entities : Entities} {rty : List (Attr × QualifiedType)} {err : Error}
  (ih : ∀ (axᵢ : Attr × Expr), axᵢ ∈ axs → TypeOfIsSound axᵢ.snd)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : List.Forall₂ (AttrExprHasAttrType c₁ env) axs rty)
  (h₄ : (axs.mapM fun x => bindAttr x.fst (evaluate x.snd request entities)) = Except.error err) :
  err = Error.entityDoesNotExist ∨ err = Error.extensionError ∨ err = Error.arithBoundsError
:= by
  cases axs
  case nil =>
    simp [List.mapM₂, List.attach₂, pure, Except.pure] at h₄
  case cons hd tl =>
    cases h₃ ; rename_i hd' tl' hh₃ ht₃
    simp [List.mapM₂, List.attach₂] at h₄
    cases h₅ : bindAttr hd.fst (evaluate hd.snd request entities) <;> simp [h₅] at h₄
    case error e =>
      simp [bindAttr] at h₅
      cases h₆ : evaluate hd.snd request entities <;> simp [h₆] at h₅
      subst h₄ h₅
      specialize ih hd
      simp only [List.mem_cons, true_or, TypeOfIsSound, forall_const] at ih
      have ⟨ty', c', _, hh₃⟩ := hh₃
      specialize ih h₁ h₂ hh₃
      have ⟨_, v, ih, _⟩ := ih
      simp [EvaluatesTo, h₆] at ih
      exact ih
    case ok vhd =>
      let f := fun (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd request entities)
      cases h₅ : tl.mapM f <;> simp [h₅, pure, Except.pure] at h₄
      rw [eq_comm] at h₄ ; subst h₄
      apply @type_of_record_is_sound_err
        tl c₁ env request entities tl' err
        (by intro axᵢ h ; apply ih ; simp [h])
        h₁ h₂ ht₃
        (by simp [List.mapM₂, List.attach₂, List.mapM_pmap_subtype f, h₅])


theorem type_of_record_is_sound {axs : List (Attr × Expr)} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.record axs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (axᵢ : Attr × Expr), axᵢ ∈ axs → TypeOfIsSound axᵢ.snd) :
  GuardedCapabilitiesInvariant (Expr.record axs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.record axs) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨h₆, rty, h₅, h₄⟩ := type_of_record_inversion h₃
  subst h₅ h₆
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    simp [EvaluatesTo, evaluate, List.mapM₂, List.attach₂]
    let f := fun (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd request entities)
    simp [List.mapM_pmap_subtype f]
    cases h₅ : (axs.mapM f) <;>
    simp [h₅]
    case error err =>
      simp [type_is_inhabited]
      exact type_of_record_is_sound_err ih h₁ h₂ h₄ h₅
    case ok avs =>
      exact type_of_record_is_sound_ok ih h₁ h₂ h₄ h₅

end Cedar.Thm
