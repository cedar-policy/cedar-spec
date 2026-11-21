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

module

public import Cedar.Thm.Validation.Relational.Soundness
import Batteries.Data.List.Lemmas
import all Cedar.Data.Set -- unfolds `any`, `union`
import all Cedar.Spec.Entities -- unfolds `tags`
import all Cedar.Validation.Typechecker -- unfolds `Capabilities`
import all Cedar.Validation.Types -- unfolds `not`, `tags`

/-! # `HasType` reads its input capabilities only up to `CapsEquiv` -/

@[expose] public section

namespace Cedar.Validation.Relational

open Cedar.Spec Cedar.Data Cedar.Validation

/-! ## Helper lemmas -/

theorem capMerge_nil_right (c : Capabilities) : CapMerge [] c c := by
  induction c with
  | nil => exact CapMerge.nil
  | cons hd tl ih => obtain ⟨x,k⟩ := hd; exact CapMerge.right x k [] tl tl ih

theorem capMerge_append (c₁ c₂ : Capabilities) : CapMerge c₁ c₂ (c₁ ++ c₂) := by
  induction c₁ with
  | nil => exact capMerge_nil_right c₂
  | cons hd tl ih => obtain ⟨x,k⟩ := hd; exact CapMerge.left x k tl c₂ (tl ++ c₂) ih

theorem capAttrMem_congr {x a c c''} (h : CapAttrMem x a c) (he : CapsEquiv c c'') :
    CapAttrMem x a c'' := capAttrMem_iff.mpr ((he _).mp (capAttrMem_iff.mp h))

theorem capTagMem_congr {x e c c''} (h : CapTagMem x e c) (he : CapsEquiv c c'') :
    CapTagMem x e c'' := capTagMem_iff.mpr ((he _).mp (capTagMem_iff.mp h))

theorem hasAttrInRecord_congr {rty x a c b ty caps c''}
    (h : HasAttrInRecord rty x a c b ty caps) (he : CapsEquiv c c'') :
    HasAttrInRecord rty x a c'' b ty caps := by
  cases h with
  | found_in_caps knownToExist qty hcap hmc =>
    exact HasAttrInRecord.found_in_caps _ _ _ _ _ _ (capAttrMem_congr hcap he) hmc
  | found_required_known ty' hmc => exact HasAttrInRecord.found_required_known _ _ _ _ _ hmc
  | found_not_known qty hmc hneg =>
    exact HasAttrInRecord.found_not_known _ _ _ _ _ hmc (fun h => hneg (capAttrMem_congr h he.symm))
  | found_optional_known ty' hmc hneg =>
    exact HasAttrInRecord.found_optional_known _ _ _ _ _ hmc (fun h => hneg (capAttrMem_congr h he.symm))

theorem getAttrInRecord_congr {rty x a c ty c''}
    (h : GetAttrInRecord rty x a c ty) (he : CapsEquiv c c'') : GetAttrInRecord rty x a c'' ty := by
  cases h with
  | required hmc => exact GetAttrInRecord.required _ _ _ _ _ hmc
  | optional hcap hmc => exact GetAttrInRecord.optional _ _ _ _ _ (capAttrMem_congr hcap he) hmc

theorem hasAttrOn_congr {env ty x a c b ci c''}
    (h : HasAttrOn env ty x a c b ci) (he : CapsEquiv c c'') : HasAttrOn env ty x a c'' b ci := by
  cases h with
  | record _ _ _ _ _ _ _ hin => exact HasAttrOn.record _ _ _ _ _ _ _ (hasAttrInRecord_congr hin he)
  | recordNotFound _ _ _ _ _ hnk => exact HasAttrOn.recordNotFound _ _ _ _ _ hnk
  | entity _ _ _ _ _ _ _ _ _ _ hma hin =>
    exact HasAttrOn.entity _ _ _ _ _ _ _ _ _ _ hma (hasAttrInRecord_congr hin he)
  | entityNotFound _ _ _ _ _ _ _ _ hma hnk => exact HasAttrOn.entityNotFound _ _ _ _ _ _ _ _ hma hnk
  | enum _ _ _ _ _ _ _ _ hme => exact HasAttrOn.enum _ _ _ _ _ _ _ _ hme
  | action _ _ _ _ _ _ _ _ _ hnc hpk => exact HasAttrOn.action _ _ _ _ _ _ _ _ _ hnc hpk

theorem getAttrOn_congr {env ty x a c aty c''}
    (h : GetAttrOn env ty x a c aty) (he : CapsEquiv c c'') : GetAttrOn env ty x a c'' aty := by
  cases h with
  | record _ _ _ _ _ _ hg => exact GetAttrOn.record _ _ _ _ _ _ (getAttrInRecord_congr hg he)
  | entity _ _ _ _ _ _ _ _ _ hma hg =>
    exact GetAttrOn.entity _ _ _ _ _ _ _ _ _ hma (getAttrInRecord_congr hg he)

/-- `c ++ c'` witnesses a `CapMerge` whose output is equivalent to that of any other
    `CapMerge c₀ c' m` with `c₀ ≈ c`. -/
theorem capMerge_append_equiv {c₀ c c' m : Capabilities} (hm : CapMerge c₀ c' m)
    (he : CapsEquiv c₀ c) : CapsEquiv m (c ++ c') :=
  (capMerge_capsEquiv_union hm).trans ((CapsEquiv.union he (CapsEquiv.refl c')).trans
    (capMerge_capsEquiv_union (capMerge_append c c')).symm)

theorem extHasAttrChain_congr {env ty x a as c b cout}
    (h : ExtHasAttrChain env ty x a as c b cout) :
    ∀ {c''}, CapsEquiv c c'' →
      ∃ cout', ExtHasAttrChain env ty x a as c'' b cout' ∧ CapsEquiv cout cout' := by
  induction h with
  | last _ _ _ _ _ _ hha =>
    intro c'' he
    exact ⟨_, ExtHasAttrChain.last _ _ _ _ _ _ _ (hasAttrOn_congr hha he), CapsEquiv.refl _⟩
  | absent _ _ _ _ _ _ _ hha =>
    intro c'' he
    exact ⟨_, ExtHasAttrChain.absent _ _ _ _ _ _ _ _ (hasAttrOn_congr hha he), CapsEquiv.refl _⟩
  | restFf _ _ _ _ _ _ _ ci _ _ _ hha hnf hm hga _ ih =>
    intro c'' he
    have hcc := capMerge_append_equiv hm he
    obtain ⟨_, hr, _⟩ := ih hcc
    exact ⟨[], ExtHasAttrChain.restFf _ _ _ _ _ _ _ _ _ _ _ _ (hasAttrOn_congr hha he) hnf
      (capMerge_append c'' ci) (getAttrOn_congr hga hcc) hr, CapsEquiv.refl _⟩
  | restTt _ _ _ _ _ _ _ ci _ _ _ _ hha hnf hm hga _ hm2 ih =>
    intro c'' he
    have hcc := capMerge_append_equiv hm he
    obtain ⟨cr', hr, hce⟩ := ih hcc
    refine ⟨ci ++ cr', ExtHasAttrChain.restTt _ _ _ _ _ _ _ _ _ _ _ _ _ (hasAttrOn_congr hha he)
      hnf (capMerge_append c'' ci) (getAttrOn_congr hga hcc) hr (capMerge_append ci cr'), ?_⟩
    exact (capMerge_capsEquiv_union hm2).trans ((CapsEquiv.union (CapsEquiv.refl ci) hce).trans
      (capMerge_capsEquiv_union (capMerge_append ci cr')).symm)
  | restAnyBool _ _ _ _ _ _ _ ci _ _ _ _ hha hnf hm hga _ hm2 ih =>
    intro c'' he
    have hcc := capMerge_append_equiv hm he
    obtain ⟨cr', hr, hce⟩ := ih hcc
    refine ⟨ci ++ cr', ExtHasAttrChain.restAnyBool _ _ _ _ _ _ _ _ _ _ _ _ _
      (hasAttrOn_congr hha he) hnf (capMerge_append c'' ci) (getAttrOn_congr hga hcc) hr
      (capMerge_append ci cr'), ?_⟩
    exact (capMerge_capsEquiv_union hm2).trans ((CapsEquiv.union (CapsEquiv.refl ci) hce).trans
      (capMerge_capsEquiv_union (capMerge_append ci cr')).symm)

/-! ## Congruence theorem -/

/-- Input-capability congruence: `HasType` consults its input capabilities only up
to set-equality (`CapsEquiv`), and its output capabilities vary only up to
set-equality when the input caps do. -/
theorem hasType_capsCongr {decl syn x c env ty cout} (h : HasType decl syn x c env ty cout) :
    ∀ {c''}, CapsEquiv c c'' → ∃ cout', HasType decl syn x c'' env ty cout' ∧ CapsEquiv cout cout' := by
  induction h using HasType.rec
    (motive_2 := fun xs c env tys _ => ∀ {c''}, CapsEquiv c c'' → HasTypeList decl syn xs c'' env tys)
    (motive_3 := fun lb axs c env atys _ => ∀ {c''}, CapsEquiv c c'' →
      HasTypeRecord decl syn lb axs c'' env atys)
    (motive_4 := fun f args c env t _ => ∀ {c''}, CapsEquiv c c'' →
      HasTypeExtCall decl syn f args c'' env t)
    (motive_5 := fun b axs c env rty _ => ∀ {c''}, CapsEquiv c c'' →
      RecordTypeOf decl syn b axs c'' env rty)
    (motive_6 := fun axs c env atys _ => ∀ {c''}, CapsEquiv c c'' →
      HasTypeFields decl syn axs c'' env atys)
    with
  -- Literals, variables, unary operators, and binary operators other than `<`, `<=` and `in`
  | litBoolTrue _ _ _ _ | litBoolFalse _ _ _ _ | litInt _ _ _ _ _ | litString _ _ _ _ _
  | litEntity _ _ _ _ _ _ _ | varPrincipal _ _ _ _ _ _ _ | varAction _ _ _ _ _ _ _ _
  | varResource _ _ _ _ _ _ _ | varContext _ _ _ _ _ _ _ =>
    intro _ _
    exact ⟨[], by constructor <;> assumption, CapsEquiv.refl []⟩
  | unaryAppNotTt _ _ _ _ ih | unaryAppNotFf _ _ _ _ ih | unaryAppNotAny _ _ _ _ ih
  | unaryAppNeg _ _ _ _ ih | unaryAppIsEmpty _ _ _ _ _ ih | unaryAppLike _ _ _ _ _ ih
  | unaryAppIsTrue _ _ _ _ _ _ ih | unaryAppIsFalse _ _ _ _ _ _ _ _ _ ih
  | binaryAppEqLitSame _ _ _ _ _ ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    exact ⟨[], by constructor <;> assumption, CapsEquiv.refl []⟩
  | binaryAppEqNonLitLub _ _ _ _ _ _ _ _ _ _ _ ih1 ih2
  | binaryAppAdd _ _ _ _ _ _ ih1 ih2
  | binaryAppSub _ _ _ _ _ _ ih1 ih2 | binaryAppMul _ _ _ _ _ _ ih1 ih2
  | binaryAppContains _ _ _ _ _ _ _ _ _ ih1 ih2 | binaryAppContainsAll _ _ _ _ _ _ _ _ _ ih1 ih2
  | binaryAppContainsAny _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by constructor <;> assumption, CapsEquiv.refl []⟩
  | binaryAppEqLitDiff p₁ p₂ c env ty₁ ty₂ a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], HasType.binaryAppEqLitDiff _ _ _ _ _ _ a h1 h2, CapsEquiv.refl []⟩
  | binaryAppEqEntityDiff x₁ x₂ c env ety₁ ety₂ a a1 a2 a3 a4 a5 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], HasType.binaryAppEqEntityDiff _ _ _ _ _ _ a a1 a2 h1 h2 a5, CapsEquiv.refl []⟩
  -- Binary: arithmetic / comparison
  | binaryAppLessInt x₁ x₂ c env a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppLessInt <;> assumption, CapsEquiv.refl []⟩
  | binaryAppLessDatetime x₁ x₂ c env a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppLessDatetime <;> assumption, CapsEquiv.refl []⟩
  | binaryAppLessDuration x₁ x₂ c env a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppLessDuration <;> assumption, CapsEquiv.refl []⟩
  | binaryAppLessEqInt x₁ x₂ c env a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppLessEqInt <;> assumption, CapsEquiv.refl []⟩
  | binaryAppLessEqDatetime x₁ x₂ c env a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppLessEqDatetime <;> assumption, CapsEquiv.refl []⟩
  | binaryAppLessEqDuration x₁ x₂ c env a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppLessEqDuration <;> assumption, CapsEquiv.refl []⟩
  -- Binary: mem (generic)
  | binaryAppMemEntityEntity x₁ x₂ c ets acts reqty ety₁ ety₂ a a1 a2 a3 a4 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppMemEntityEntity <;> assumption, CapsEquiv.refl []⟩
  | binaryAppMemEntitySame x₁ x₂ c ets acts reqty ety a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppMemEntitySame <;> assumption, CapsEquiv.refl []⟩
  | binaryAppMemEntitySet x₁ x₂ c ets acts reqty ety₁ ety₂ a a1 a2 a3 a4 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppMemEntitySet <;> assumption, CapsEquiv.refl []⟩
  | binaryAppMemEntitySetSame x₁ x₂ c ets acts reqty ety a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppMemEntitySetSame <;> assumption, CapsEquiv.refl []⟩
  | binaryAppMemEntityEntityFf x₁ x₂ c ets acts reqty ety₁ ety₂ a a1 a2 a3 a4 a5 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], HasType.binaryAppMemEntityEntityFf _ _ _ _ _ _ _ _ a a1 a2 a3 h1 h2,
      CapsEquiv.refl []⟩
  | binaryAppMemEntitySetFf x₁ x₂ c ets acts reqty ety₁ ety₂ a a1 a2 a3 a4 a5 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], HasType.binaryAppMemEntitySetFf _ _ _ _ _ _ _ _ a a1 a2 a3 h1 h2,
      CapsEquiv.refl []⟩
  -- Binary: mem (action literal)
  | binaryAppMemActionLitTt uid₁ uid₂ c ets acts reqty a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppMemActionLitTt <;> assumption, CapsEquiv.refl []⟩
  | binaryAppMemActionLitFf uid₁ uid₂ c ets acts reqty a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppMemActionLitFf <;> assumption, CapsEquiv.refl []⟩
  | binaryAppMemActionLitSetTt uid₁ xs c ets acts reqty ety₂ a1 a2 a3 a4 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppMemActionLitSetTt <;> assumption, CapsEquiv.refl []⟩
  | binaryAppMemActionLitSetFf uid₁ xs c ets acts reqty ety₂ a1 a2 a3 a4 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppMemActionLitSetFf <;> assumption, CapsEquiv.refl []⟩
  | binaryAppMemActionEntityFf x₁ x₂ c ets acts reqty ety₁ ety₂ a a1 a2 a3 a4 a5 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppMemActionEntityFf <;> assumption, CapsEquiv.refl []⟩
  | binaryAppMemActionSetFf x₁ x₂ c ets acts reqty ety₁ ety₂ a a1 a2 a3 a4 a5 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.binaryAppMemActionSetFf <;> assumption, CapsEquiv.refl []⟩
  -- hasAttr / getAttr
  | hasAttrRecord x₁ a c env rty ty caps a1 a2 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    exact ⟨caps, HasType.hasAttrRecord _ _ _ _ _ _ _ h1 (hasAttrInRecord_congr a2 he),
      CapsEquiv.refl caps⟩
  | hasAttrRecordNotFound x₁ a c env rty a1 a2 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    exact ⟨[], by apply HasType.hasAttrRecordNotFound <;> assumption, CapsEquiv.refl []⟩
  | hasAttrEntity x₁ a c ets acts reqty ety ty caps rty a1 a2 a3 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    exact ⟨caps, HasType.hasAttrEntity _ _ _ _ _ _ _ _ _ _ a1 h1 (hasAttrInRecord_congr a3 he),
      CapsEquiv.refl caps⟩
  | hasAttrEntityNotFound x₁ a c ets acts reqty ety rty a1 a2 a3 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    exact ⟨[], by apply HasType.hasAttrEntityNotFound <;> assumption, CapsEquiv.refl []⟩
  | hasAttrEnum x₁ a c ets acts reqty ety eids a1 a2 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    exact ⟨[], by apply HasType.hasAttrEnum <;> assumption, CapsEquiv.refl []⟩
  | hasAttrActionFf x₁ attr c ets acts reqty ety eid entry hnc hpk hht ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    exact ⟨[], by apply HasType.hasAttrActionFf <;> assumption, CapsEquiv.refl []⟩
  | getAttrRecord x₁ a c env rty ty a1 a2 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    exact ⟨[], HasType.getAttrRecord _ _ _ _ _ _ h1 (getAttrInRecord_congr a2 he),
      CapsEquiv.refl []⟩
  | getAttrEntity x₁ a c ets acts reqty ety ty rty a1 a2 a3 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    exact ⟨[], HasType.getAttrEntity _ _ _ _ _ _ _ _ _ a1 h1 (getAttrInRecord_congr a3 he),
      CapsEquiv.refl []⟩
  -- hasTag / getTag
  | hasTagAnyBool x₁ x₂ c ets acts reqty ety ty a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨_, HasType.hasTagAnyBool _ _ _ _ _ _ _ _ a
      (fun hc => a1 (capTagMem_congr hc he.symm)) h1 h2, CapsEquiv.refl _⟩
  | hasTagTt x₁ x₂ c ets acts reqty ety ty a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], HasType.hasTagTt _ _ _ _ _ _ _ _ (capTagMem_congr a he) a1 h1 h2,
      CapsEquiv.refl []⟩
  | hasTagFf x₁ x₂ c ets acts reqty ety a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.hasTagFf <;> assumption, CapsEquiv.refl []⟩
  | hasTagActionFf x₁ x₂ c ets acts reqty ety eid entry a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.hasTagActionFf <;> assumption, CapsEquiv.refl []⟩
  | getTag x₁ x₂ c ets acts reqty ety ty a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], HasType.getTag _ _ _ _ _ _ _ _ (capTagMem_congr a he) a1 h1 h2,
      CapsEquiv.refl []⟩
  -- ite
  | iteTt x₁ x₂ x₃ c env c₁ c_c₁ t₂ c₂ cout a a1 a2 a3 a4 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append c'' c₁')).symm)
    obtain ⟨c₂', h2, hc2⟩ := ih2 hb
    exact ⟨c₁' ++ c₂', HasType.iteTt _ _ _ _ _ _ _ _ _ _ h1 (capMerge_append c'' c₁') h2
      (capMerge_append c₁' c₂') a4, (capMerge_capsEquiv_union a3).trans ((CapsEquiv.union hc1 hc2).trans
        (capMerge_capsEquiv_union (capMerge_append c₁' c₂')).symm)⟩
  | iteFf x₁ x₂ x₃ c env c₁ t₃ c₃ a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨c₃', h3, hc3⟩ := ih2 he
    exact ⟨c₃', HasType.iteFf _ _ _ _ _ _ _ _ h1 h3 a2, hc3⟩
  | iteAnyBool x₁ x₂ x₃ c env c₁ c_c₁ t₂ c₂ t₃ c₃ lubTy c₁₂ a a1 a2 a3 a4 a5 ih1 ih2 ih3 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append c'' c₁')).symm)
    obtain ⟨c₂', h2, hc2⟩ := ih2 hb
    obtain ⟨c₃', h3, hc3⟩ := ih3 he
    exact ⟨capIntersect (c₁' ++ c₂') c₃',
      HasType.iteAnyBool _ _ _ _ _ _ _ _ _ _ _ _ _ h1 (capMerge_append c'' c₁') h2 h3 a4
        (capMerge_append c₁' c₂'),
      (capIntersect_capsEquiv_inter c₁₂ c₃).trans ((CapsEquiv.inter
        ((capMerge_capsEquiv_union a5).trans ((CapsEquiv.union hc1 hc2).trans
          (capMerge_capsEquiv_union (capMerge_append c₁' c₂')).symm)) hc3).trans
        (capIntersect_capsEquiv_inter (c₁' ++ c₂') c₃').symm)⟩
  -- and
  | andShort x₁ x₂ c env c₁ a a1 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    exact ⟨[], by apply HasType.andShort <;> assumption, CapsEquiv.refl []⟩
  | andTtFf x₁ x₂ c env c₁ c_c₁ c₂ a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append c'' c₁')).symm)
    obtain ⟨c₂', h2, _⟩ := ih2 hb
    exact ⟨[], HasType.andTtFf _ _ _ _ _ _ _ h1 (capMerge_append c'' c₁') h2, CapsEquiv.refl []⟩
  | andTtTt x₁ x₂ c env c₁ c_c₁ c₂ cout a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append c'' c₁')).symm)
    obtain ⟨c₂', h2, hc2⟩ := ih2 hb
    exact ⟨c₁' ++ c₂', HasType.andTtTt _ _ _ _ _ _ _ _ h1 (capMerge_append c'' c₁') h2
      (capMerge_append c₁' c₂'), (capMerge_capsEquiv_union a3).trans ((CapsEquiv.union hc1 hc2).trans
        (capMerge_capsEquiv_union (capMerge_append c₁' c₂')).symm)⟩
  | andTtAny x₁ x₂ c env c₁ c_c₁ c₂ cout a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append c'' c₁')).symm)
    obtain ⟨c₂', h2, hc2⟩ := ih2 hb
    exact ⟨c₁' ++ c₂', HasType.andTtAny _ _ _ _ _ _ _ _ h1 (capMerge_append c'' c₁') h2
      (capMerge_append c₁' c₂'), (capMerge_capsEquiv_union a3).trans ((CapsEquiv.union hc1 hc2).trans
        (capMerge_capsEquiv_union (capMerge_append c₁' c₂')).symm)⟩
  | andAnyFf x₁ x₂ c env c₁ c_c₁ c₂ a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append c'' c₁')).symm)
    obtain ⟨c₂', h2, _⟩ := ih2 hb
    exact ⟨[], HasType.andAnyFf _ _ _ _ _ _ _ h1 (capMerge_append c'' c₁') h2, CapsEquiv.refl []⟩
  | andAnyTt x₁ x₂ c env c₁ c_c₁ c₂ cout a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append c'' c₁')).symm)
    obtain ⟨c₂', h2, hc2⟩ := ih2 hb
    exact ⟨c₁' ++ c₂', HasType.andAnyTt _ _ _ _ _ _ _ _ h1 (capMerge_append c'' c₁') h2
      (capMerge_append c₁' c₂'), (capMerge_capsEquiv_union a3).trans ((CapsEquiv.union hc1 hc2).trans
        (capMerge_capsEquiv_union (capMerge_append c₁' c₂')).symm)⟩
  | andAnyAny x₁ x₂ c env c₁ c_c₁ c₂ cout a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append c'' c₁')).symm)
    obtain ⟨c₂', h2, hc2⟩ := ih2 hb
    exact ⟨c₁' ++ c₂', HasType.andAnyAny _ _ _ _ _ _ _ _ h1 (capMerge_append c'' c₁') h2
      (capMerge_append c₁' c₂'), (capMerge_capsEquiv_union a3).trans ((CapsEquiv.union hc1 hc2).trans
        (capMerge_capsEquiv_union (capMerge_append c₁' c₂')).symm)⟩
  -- or
  | orShort x₁ x₂ c env c₁ a a1 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    exact ⟨[], by apply HasType.orShort <;> assumption, CapsEquiv.refl []⟩
  | orFfThen x₁ x₂ c env c₁ b₂ c₂ a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨c₂', h2, hc2⟩ := ih2 he
    exact ⟨c₂', HasType.orFfThen _ _ _ _ _ _ _ h1 h2, hc2⟩
  | orAnyTt x₁ x₂ c env c₁ c₂ a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], by apply HasType.orAnyTt <;> assumption, CapsEquiv.refl []⟩
  | orAnyFf x₁ x₂ c env c₁ c₂ a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨c₁', HasType.orAnyFf _ _ _ _ _ _ h1 h2, hc1⟩
  | orAnyAny x₁ x₂ c env c₁ c₂ a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    obtain ⟨c₂', h2, hc2⟩ := ih2 he
    exact ⟨capIntersect c₁' c₂', HasType.orAnyAny _ _ _ _ _ _ h1 h2,
      (capIntersect_capsEquiv_inter c₁ c₂).trans ((CapsEquiv.inter hc1 hc2).trans
        (capIntersect_capsEquiv_inter c₁' c₂').symm)⟩
  -- set / record / callExt
  | set x xs c env ty tyList lubTy a a1 a2 ih_x ih_xs =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih_x he
    exact ⟨[], HasType.set _ _ _ _ _ _ _ h1 (ih_xs he) a2, CapsEquiv.refl []⟩
  | record axs c env rty a ih =>
    intro c'' he
    exact ⟨[], HasType.record _ _ _ _ (ih he), CapsEquiv.refl []⟩
  -- RecordTypeOf (motive_5)
  | sorted b axs axs' c env atyList a1 a2 ih =>
    rename_i c'' he
    exact RecordTypeOf.sorted _ _ _ _ _ _ a1 (ih he)
  | lax axs c env atys a ih =>
    rename_i c'' he
    exact RecordTypeOf.lax _ _ _ _ (ih he)
  | callExt xfn args c env ty a ih =>
    intro c'' he
    exact ⟨[], HasType.callExt _ _ _ _ _ (ih he), CapsEquiv.refl []⟩
  -- HasTypeList (motive_2)
  | nil c env =>
    rename_i he
    exact HasTypeList.nil _ _
  | cons x xs c env ty tys a a1 ih1 ih2 =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih1 he
    exact HasTypeList.cons _ _ _ _ _ _ h1 (ih2 he)
  -- HasTypeExtCall (motive_4)
  | decimal _ _ _ a | ip _ _ _ a | datetime _ _ _ a | duration _ _ _ a =>
    constructor; exact a
  | lessThan _ _ _ _ _ _ ih_a ih_b | lessThanOrEqual _ _ _ _ _ _ ih_a ih_b
  | greaterThan _ _ _ _ _ _ ih_a ih_b | greaterThanOrEqual _ _ _ _ _ _ ih_a ih_b
  | offset _ _ _ _ _ _ ih_a ih_b | durationSince _ _ _ _ _ _ ih_a ih_b =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    obtain ⟨_, h2, _⟩ := ih_b he
    constructor <;> assumption
  | isIpv4 _ _ _ _ ih_a | isIpv6 _ _ _ _ ih_a | isLoopback _ _ _ _ ih_a
  | isMulticast _ _ _ _ ih_a | toDate _ _ _ _ ih_a | toTime _ _ _ _ ih_a
  | toMilliseconds _ _ _ _ ih_a | toSeconds _ _ _ _ ih_a | toMinutes _ _ _ _ ih_a
  | toHours _ _ _ _ ih_a | toDays _ _ _ _ ih_a =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    constructor; exact h1
  | isInRange a xs c env tys ha hip hxs ih_a ih_xs =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    exact HasTypeExtCall.isInRange _ _ _ _ _ h1 hip (ih_xs he)
  | extHasAttr x₁ a as c env ty₁ oc b cout a1 a2 a3 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    obtain ⟨cout', h2, hce⟩ := extHasAttrChain_congr a2 he
    exact ⟨cout', HasType.extHasAttr _ _ _ _ _ _ _ _ _ h1 h2 a3, hce⟩
  -- HasTypeRecord (motive_3) and HasTypeFields (motive_6): nil / cons — share recursor tags
  -- with HasTypeList.
  | _ =>
    first
    | (intro _he; exact HasTypeRecord.nil _ _ _)
    | (rename_i hka hHT hHTR aih
       intro ihR c'' he
       obtain ⟨_, hx, _⟩ := aih he
       exact HasTypeRecord.cons _ _ _ _ _ _ _ _ hka hx (ihR he))
    | (exact HasTypeFields.nil _ _)
    | (rename_i hHT hFs aih ihF c''
       intro he
       obtain ⟨_, hx, _⟩ := aih he
       exact HasTypeFields.cons _ _ _ _ _ _ _ hx (ihF he))

end Cedar.Validation.Relational
