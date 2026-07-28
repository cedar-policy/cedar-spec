import CedarFFI.TypedExprDRT
open Cedar.Spec Cedar.Validation CedarFFI
def tBool : CedarType := .bool .anyBool
def tStr  : CedarType := .string
#eval Lean.toJson (TypedExpr.unaryApp (.like ([PatElem.star, PatElem.justChar 'a'])) (.lit (.string "s") tStr) tBool)
#eval Lean.toJson (TypedExpr.getAttr (.var .principal (.entity {id := "U", path := []})) "name" tStr)
