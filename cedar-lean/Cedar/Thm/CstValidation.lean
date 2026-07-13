import Cedar.Spec.Cst
import Cedar.Spec.CstSemantics
import Cedar.Spec.CstToAst
import Cedar.Thm.Translation
import Cedar.Thm.Validation

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/-- If a translated CST expression is well-typed, evaluating the CST expression
never throws a `typeError`. -/
theorem cst_validated_no_type_error
    {cst : Cst.Expr} {ast : Spec.Expr} {c₁ c₂ : Capabilities} {ty : TypedExpr}
    {env : TypeEnv} {request : Request} {entities : Entities}
    (htrans : cst.toAExpr? = some ast)
    (hcap : CapabilitiesInvariant c₁ request entities)
    (hwf : InstanceOfWellFormedEnvironment request entities env)
    (hwt : typeOf ast c₁ env = .ok (ty, c₂)) :
    cst.evaluate request entities ≠ .error .typeError := by
  intro hcontra
  obtain ⟨_, v, hev, _⟩ := type_of_is_sound hcap hwf hwt
  have hast : evaluate ast request entities = .error .typeError := by
    rw [expr_to_expr_sound htrans, hcontra]
  simp [EvaluatesTo, hast] at hev

/--
**CST validation soundness (policy-set level).** The CST counterpart of
`validation_is_sound`: if a set of CST policies translates to a set of AST
policies that is well-typed (valid) with respect to the schema, and the request
and entities are consistent with the schema, then evaluating each CST policy's
expression never throws a `typeError` (it produces a boolean value or one of the
runtime-only errors `entityDoesNotExist`, `extensionError`, `arithBoundsError`). -/

theorem cst_validation_is_sound (cps : Cst.Policies) (aps : Policies)
    (schema : Schema) (request : Request) (entities : Entities) :
    cps.toPolicies? = some aps →
    schema.validateWellFormed = .ok () →
    validate aps schema = .ok () →
    validateRequest schema request = .ok () →
    validateEntities schema entities = .ok () →
    ∀ cp ∈ cps.ps, cp.toExpr.evaluate request entities ≠ .error .typeError := by
  intro htrans hwf hval hreq hent cp hcp
  have hbool := validation_is_sound aps schema request entities hwf hval hreq hent
  obtain ⟨ap, hap_mem, hcp_ap⟩ :=
    List.forall₂_implies_all_left (toPolicies?_forall₂ htrans) cp hcp
  obtain ⟨_, hev⟩ := hbool ap hap_mem
  obtain ⟨ae, hae⟩ := toPolicy?_implies_toAExpr? hcp_ap
  have h1 : evaluate ae request entities = cp.toExpr.evaluate request entities :=
    expr_to_expr_sound hae
  have h2 : evaluate ae request entities = evaluate ap.toExpr request entities :=
    policy_to_expr_sound cp ap cp.toExpr ae request entities hcp_ap rfl hae
  intro hcontra
  have hap_te : evaluate ap.toExpr request entities = .error .typeError := by
    rw [← h2, h1]; exact hcontra
  simp [EvaluatesTo, hap_te] at hev

end Cedar.Thm
