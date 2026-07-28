import CedarFFI.TypedExprDRT
open Cedar.Spec Cedar.Validation CedarFFI

def ety : EntityType := { id := "User", path := ["NS"] }
def uid : EntityUID := { ty := ety, eid := "alice" }

-- every CedarType shape
def tBool : CedarType := .bool .anyBool
def tTT   : CedarType := .bool .tt
def tInt  : CedarType := .int
def tStr  : CedarType := .string
def tEnt  : CedarType := .entity ety
def tSet  : CedarType := .set .int
def tRec  : CedarType := .record (Cedar.Data.Map.mk [("a", .required .int), ("b", .optional .string)])
def tExt  : CedarType := .ext .decimal

#eval Lean.toJson tBool
#eval Lean.toJson tTT
#eval Lean.toJson tInt
#eval Lean.toJson tStr
#eval Lean.toJson tEnt
#eval Lean.toJson tSet
#eval Lean.toJson tRec
#eval Lean.toJson tExt

-- every TypedExpr constructor
#eval Lean.toJson (TypedExpr.lit (.bool true) tBool)
#eval Lean.toJson (TypedExpr.lit (.int 1) tInt)
#eval Lean.toJson (TypedExpr.lit (.string "s") tStr)
#eval Lean.toJson (TypedExpr.lit (.entityUID uid) tEnt)
#eval Lean.toJson (TypedExpr.var .principal tEnt)
#eval Lean.toJson (TypedExpr.var .context tRec)
#eval Lean.toJson (TypedExpr.ite (.lit (.bool true) tBool) (.lit (.int 1) tInt) (.lit (.int 2) tInt) tInt)
#eval Lean.toJson (TypedExpr.and (.lit (.bool true) tBool) (.lit (.bool false) tBool) tBool)
#eval Lean.toJson (TypedExpr.or (.lit (.bool true) tBool) (.lit (.bool false) tBool) tBool)
#eval Lean.toJson (TypedExpr.unaryApp .not (.lit (.bool true) tBool) tBool)
#eval Lean.toJson (TypedExpr.unaryApp .neg (.lit (.int 1) tInt) tInt)
#eval Lean.toJson (TypedExpr.unaryApp .isEmpty (.set [] tSet) tBool)
#eval Lean.toJson (TypedExpr.unaryApp (.like (Cedar.Spec.Pattern.mk [.star, .justChar 'a'])) (.lit (.string "s") tStr) tBool)
#eval Lean.toJson (TypedExpr.unaryApp (.is ety) (.lit (.entityUID uid) tEnt) tBool)
#eval Lean.toJson (TypedExpr.binaryApp .less (.lit (.int 1) tInt) (.lit (.int 2) tInt) tBool)
#eval Lean.toJson (TypedExpr.binaryApp .mem (.lit (.entityUID uid) tEnt) (.lit (.entityUID uid) tEnt) tBool)
#eval Lean.toJson (TypedExpr.getAttr (.var .context tRec) "a" tInt)
#eval Lean.toJson (TypedExpr.hasAttr (.var .context tRec) "b" tBool)
#eval Lean.toJson (TypedExpr.set [(.lit (.int 1) tInt)] tSet)
#eval Lean.toJson (TypedExpr.record [("a", .lit (.int 1) tInt), ("b", .lit (.string "x") tStr)] tRec)
#eval Lean.toJson (TypedExpr.call .decimal [(.lit (.string "1.0") tStr)] tExt)
#eval Lean.toJson (TypedExpr.call .lessThan [(.lit (.string "1.0") tStr), (.lit (.string "2.0") tStr)] tBool)
