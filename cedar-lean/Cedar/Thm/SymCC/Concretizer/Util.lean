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
import Cedar.Thm.SymCC.Data
import Cedar.Thm.SymCC.Term.WF

/-!
This file contains helper lemmas that are shared by concretization proofs.
-/

namespace Cedar.Thm
open Data Spec SymCC Factory

theorem concretize?_ρ_some_eq {ρ : SymRequest} {r : Request} :
  ρ.concretize? = .some r →
  ∃ uidₚ uidₐ uidᵣ ctx,
    ρ.principal.entityUID? = .some uidₚ ∧
    ρ.action.entityUID? = .some uidₐ ∧
    ρ.resource.entityUID? = .some uidᵣ ∧
    ρ.context.recordValue? = .some ctx ∧
    r = {principal := uidₚ, action := uidₐ, resource := uidᵣ, context := ctx}
:= by
  intro h
  simp only [SymRequest.concretize?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  replace ⟨uidₚ, hp, uidₐ, ha, uidᵣ, hr, ctx, hc, h⟩ := h
  simp only [hp, Option.some.injEq, ha, hr, hc, exists_and_left, exists_eq_left', h]

theorem concretize?_εs_some_eq {uids : Set EntityUID} {εs : SymEntities} {es : Entities} :
  εs.concretize? uids = .some es →
   ∃ eds,
    (uids ∪ εs.entityUIDs).elts.mapM (SymEntities.concretize?.entityData? εs) = some eds ∧
    Map.make eds = es
:= by
  intro hs
  simp only [SymEntities.concretize?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at hs
  exact hs

theorem concretize?_entityData?_some_eq {uid : EntityUID} {ed : EntityUID × EntityData} {εs : SymEntities} :
  SymEntities.concretize?.entityData? εs uid = some ed →
  ∃ δ d,
    Map.find? εs uid.ty = some δ ∧
    SymEntityData.concretize? uid δ = some d ∧
    (uid, d) = ed
:= by
  intro hs
  simp only [SymEntities.concretize?.entityData?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at hs
  simp only [exists_and_left, hs]

theorem concretize?_δ_isValidEntityUID_implies_wfl {uid : EntityUID} {δ : SymEntityData} {εs : SymEntities} :
  Map.find? εs uid.ty = some δ →
  SymEntityData.concretize?.isValidEntityUID uid δ = true →
  Term.WellFormedLiteral εs (Term.entity uid)
:= by
  intro hf hvu
  simp only [Term.WellFormedLiteral, Term.isLiteral, and_true]
  apply Term.WellFormed.prim_wf
  apply TermPrim.WellFormed.entity_wf
  simp only [SymEntities.isValidEntityUID, hf]
  simp only [SymEntityData.concretize?.isValidEntityUID] at hvu
  exact hvu

theorem wf_δ_implies_wf_app_attrs {uid : EntityUID} {δ : SymEntityData} {εs : SymEntities} :
  δ.WellFormed εs uid.ty →
  (Term.entity uid).WellFormed εs →
  (app δ.attrs (Term.entity uid)).WellFormed εs ∧
  (app δ.attrs (Term.entity uid)).typeOf = δ.attrs.outType
:= by
  intro hwδ hwu
  apply wf_app hwu _ hwδ.left
  simp only [Term.typeOf, TermPrim.typeOf, hwδ.right.left]

theorem wf_δ_implies_wf_app_ancs {uid : EntityUID} {δ : SymEntityData} {εs : SymEntities} {ancTy : EntityType} {ancUF : UnaryFunction} :
  δ.WellFormed εs uid.ty →
  (Term.entity uid).WellFormed εs →
  δ.ancestors.find? ancTy = ancUF →
  (app ancUF (Term.entity uid)).WellFormed εs ∧
  (app ancUF (Term.entity uid)).typeOf = .set (.entity ancTy)
:= by
  intro hwδ hwu hf
  replace hwδ := hwδ.right.right.right.left ancTy ancUF hf
  rw [← hwδ.right.right]
  apply wf_app hwu _ hwδ.left
  simp only [Term.typeOf, TermPrim.typeOf, hwδ.right.left]

theorem wf_δ_implies_wf_app_tags_keys {uid : EntityUID} {δ : SymEntityData} {τs : SymTags} :
  δ.WellFormed εs uid.ty →
  (Term.entity uid).WellFormed εs →
  δ.tags = .some τs →
  (app τs.keys (Term.entity uid)).WellFormed εs ∧
  (app τs.keys (Term.entity uid)).typeOf = .set .string
:= by
  intro hwδ hwu hτs
  replace hwδ := hwδ.right.right.right.right.right.left τs hτs
  rw [← hwδ.right.right.left]
  apply wf_app hwu _ hwδ.left
  simp only [Term.typeOf, TermPrim.typeOf, hwδ.right.left]

theorem lit_tagOf (uid : EntityUID) (tag : Tag) :
  (tagOf (Term.entity uid) (Term.string tag)).isLiteral
:= by
  simp only [tagOf, Term.isLiteral, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec,
    Term.prim.sizeOf_spec, TermPrim.entity.sizeOf_spec, TermPrim.string.sizeOf_spec,
    List.nil.sizeOf_spec, List.attach₃, List.pmap, List.all_cons, List.all_nil, Bool.and_self]

end Cedar.Thm
