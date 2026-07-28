import CedarFFI.TypedExprDRT
open Cedar.Spec Cedar.Validation CedarFFI

-- A small TypedExpr: (true && 1 < 2) with annotations
def sample : TypedExpr :=
  .and
    (.lit (.bool true) (.bool .anyBool))
    (.binaryApp .less (.lit (.int 1) .int) (.lit (.int 2) .int) (.bool .anyBool))
    (.bool .anyBool)

#eval Lean.toJson sample
#eval Lean.toJson ({ principal := "P", action := "A", resource := "R", ok := true, typedExpr := some sample } : TypedExprEnvResult)
