/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Lean.Data.Json.Parser
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson
import Lean.Data.AssocList
import Lean.Data.RBMap

import Cedar.Data
import Cedar.Spec
import Cedar.Spec.Ext

namespace DiffTest

open Cedar.Spec
open Cedar.Data
open Cedar.Spec.Ext

def unwrapExcept (e: Except String Lean.Json) : Lean.Json := match e.isOk with
  | true => Option.get! e.toOption
  | false => panic! "unwrapExcept: is not ok"

def strNodeToString (node : Lean.Json) : String := match node with
  | Lean.Json.str s => s
  | _ => panic! "strNodeToString"

def jsonToEUID (json : Except String Lean.Json) : EntityUID := match json.isOk with
  | false => panic! "sorry"
  | true =>
    let json := Option.get! json.toOption
    let eid := (match unwrapExcept (json.getObjVal? "eid") with
      | Lean.Json.str str => str
      | _ => panic! json.pretty)
    match json.getObjVal? "ty" with
    | .error _ => {
      ty := {
        id := "Unspecified",
        path := []
      },
      eid := eid
    }
    | .ok (Lean.Json.str str) => {
      ty := {
        id := str,
        path := []
      },
      eid := eid
    }
    | .ok _ =>
      let ty := (unwrapExcept (json.getObjVal? "ty")).getObjVal? "Concrete"
      let ty := Option.get! ty.toOption
      match (unwrapExcept (ty.getObjVal? "id")), (unwrapExcept (ty.getObjVal? "path")) with
        | Lean.Json.str id, Lean.Json.arr path_json =>
          let path := List.map strNodeToString path_json.toList
          {
            ty := {
              id := id,
              path := path
            },
            eid := eid
          }
        | _,_ => panic! "sorry"

def litHelper (json : Except String Lean.Json) : Expr := match json.isOk with
  | false => panic! "litHelper: is not ok"
  | true => let json := Option.get! json.toOption
  match json with
    | Lean.Json.bool b => .lit (.bool b)
    | Lean.Json.num n => match n.exponent with
      | 0 => .lit (.int (Int64.mk! n.mantissa))
      | _ => panic! "litHelper: num has exponent: " ++ json.pretty
    | Lean.Json.str s => .lit (.string s)
    | _ => panic! "litHelper: not known format for json: " ++ json.pretty

def handleLit (json : Except String Lean.Json) : Expr := match json.isOk with
  | false => panic! "handleLit: not ok json"
  | true => let json := Option.get! json.toOption
  match (json.getObjVal? "Bool").isOk with
    | true => litHelper (json.getObjVal? "Bool")
    | false => match (json.getObjVal? "Long").isOk with
      | true => litHelper (json.getObjVal? "Long")
      | false => match (json.getObjVal? "String").isOk with
        | true => litHelper (json.getObjVal? "String")
        | false => match (json.getObjVal? "EntityUID").isOk with
          | true => .lit (.entityUID (jsonToEUID (json.getObjVal? "EntityUID")))
          | false => panic! "handleLit: not known format" ++ json.pretty

def handleWildcardObj (json : Lean.Json) : PatElem := match json with
| Lean.Json.str "Wildcard" => .star
| Lean.Json.obj _ => match (json.getObjVal? "Char") with
  | .ok (Lean.Json.num n) => match n.exponent with
    | 0 => .justChar (Char.ofNat (n.mantissa.toNat))
    | _ => panic! "handleWildcardObj: non zero exponent: " ++ json.pretty
  | _ => panic! "handleWildcardObj: something unknown in wildcard: " ++ json.pretty
| _ => panic! "handleWildcardObj: " ++ json.pretty

def arrayToKVPairList (json : Array Lean.Json) : Prod (List Lean.Json) (List Lean.Json) :=
List.unzip (List.map (fun x => match x with
                                      | Lean.Json.arr kv => (kv[0]!, kv[1]!)
                                      | _ => panic! "arrayToKVPairList: " ++ x.pretty) json.toList)

-- Need to convert JSON structure to Expr structure. We expect JSON to have format:
--
-- "Expr": {
-- "Lit" : { "Bool" | "Long" | "String" | "EntityUID" : blah}
-- "Var" : { "Principal" | "Action" | "Resource" | "Context" }
-- "If" : {"test_expr": Expr, "then_expr": Expr, "else_expr": Expr}
-- "And" : {"left": Expr, "right": Expr}
-- "Or" : {"left": Expr, "right": Expr}
-- "UnaryApp" : {"op": UnaryOp, "arg": Expr}
-- "BinaryApp" : {"op": UnaryOp, "arg1": Expr, "arg2": Expr}
-- "GetAttr" : {"expr": Expr, "attr": String}
-- "HasAttr" : {"expr": Expr, "arg": String}
-- "Set" : {[Expr]}
-- "Record" : {"pairs": ["id": Expr]}
-- }

/-
defined as partial to avoid writing the proof of termination, which isn't really required
as we don't need to prove correctness of the parser -- no proofs involve the parser, and
we can be confident it terminates :)
-/
partial def jsonToExpr (json : Except String Lean.Json) : Expr := match json.isOk with
  | false => panic! "sorry"
  | true =>
  let json := Option.get! json.toOption
  let json := unwrapExcept (json.getObjVal? "expr_kind")
  match json with
  | Lean.Json.null => panic! "sorry"
  | Lean.Json.bool b => .lit (.bool b)
  | Lean.Json.num n => match n.exponent with
    | 0 => .lit (.int (Int64.mk! n.mantissa))
    | _ => panic! "sorry"
  | Lean.Json.str s => .lit (.string s)
  | Lean.Json.arr _ => panic! "sorry"
  | _ =>
    match (json.getObjVal? "Lit").isOk with
    | true => handleLit (json.getObjVal? "Lit")
    | false => match (json.getObjVal? "Var").isOk with
      | true =>
        let v := unwrapExcept (json.getObjVal? "Var")
        match v with
        | Lean.Json.str s => match s with
          | "principal" => .var .principal
          | "action" => .var .action
          | "resource" => .var .resource
          | "context" => .var .context
          | _ => panic! "unknown string in var"
        | _ => panic! "var not string"
      | false => match (json.getObjVal? "And").isOk with
        | true =>
          let lhs := (unwrapExcept (json.getObjVal? "And")).getObjVal? "left"
          let rhs := (unwrapExcept (json.getObjVal? "And")).getObjVal? "right"
          .and (jsonToExpr lhs) (jsonToExpr rhs)
        | false => match (json.getObjVal? "Or").isOk with
          | true =>
            let lhs := (unwrapExcept (json.getObjVal? "Or")).getObjVal? "left"
            let rhs := (unwrapExcept (json.getObjVal? "Or")).getObjVal? "right"
            .or (jsonToExpr lhs) (jsonToExpr rhs)
          | false => match (json.getObjVal? "If").isOk with
            | true =>
              let g := (unwrapExcept (json.getObjVal? "If")).getObjVal? "test_expr"
              let t := (unwrapExcept (json.getObjVal? "If")).getObjVal? "then_expr"
              let e := (unwrapExcept (json.getObjVal? "If")).getObjVal? "else_expr"
              .ite (jsonToExpr g) (jsonToExpr t) (jsonToExpr e)
            | false => match (json.getObjVal? "UnaryApp").isOk with
              | true =>
                let json := unwrapExcept (json.getObjVal? "UnaryApp")
                match (json.getObjVal? "op").isOk, (json.getObjVal? "arg").isOk with
                | true, true =>
                  let objVal := Option.get! (json.getObjVal? "op").toOption
                  let arg := json.getObjVal? "arg"
                  match objVal with
                  | Lean.Json.str s => match s with
                    | "Not" => .unaryApp .not (jsonToExpr arg)
                    | "Neg" => .unaryApp .neg (jsonToExpr arg)
                    | _ => panic! "unknown unary op"
                  | _ => panic! "incorrect op for unary app"
                | _ , _ => panic! "unary app does not have right fields: " ++ json.pretty
              | false => match (json.getObjVal? "MulByConst").isOk with
                | true =>
                  let json := Option.get! (json.getObjVal? "MulByConst").toOption
                  let arg := json.getObjVal? "arg"
                  let constJson := unwrapExcept (json.getObjVal? "constant")
                  match constJson with
                  | Lean.Json.num n => match n.exponent with
                    | 0 => .unaryApp (.mulBy (Int64.mk! n.mantissa)) (jsonToExpr arg)
                    | _ => panic! "sorry"
                  | _ => panic! "constant for mul by is not a numebr"
                | false => match (json.getObjVal? "Like").isOk with
                  | true =>
                    let json := Option.get! (json.getObjVal? "Like").toOption
                    let expr := jsonToExpr (json.getObjVal? "expr")
                    match (json.getObjVal? "pattern") with
                      | .ok (Lean.Json.arr arr) => .unaryApp (.like (List.map handleWildcardObj arr.toList)) expr
                      | _ => panic! "not an array in Like"
                  | false => match (json.getObjVal? "BinaryApp").isOk with
                    | true =>
                      let json := unwrapExcept (json.getObjVal? "BinaryApp")
                      let op := unwrapExcept (json.getObjVal? "op")
                      let arg1 := jsonToExpr (json.getObjVal? "arg1")
                      let arg2 := jsonToExpr (json.getObjVal? "arg2")
                      match op with
                      | Lean.Json.str s => match s with
                        | "Eq" => .binaryApp .eq arg1 arg2
                        | "In" => .binaryApp .mem arg1 arg2
                        | "Less" => .binaryApp .less arg1 arg2
                        | "LessEq" => .binaryApp .lessEq arg1 arg2
                        | "Add" => .binaryApp .add arg1 arg2
                        | "Sub" => .binaryApp .sub arg1 arg2
                        | "Contains" => .binaryApp .contains arg1 arg2
                        | "ContainsAll" => .binaryApp .containsAll arg1 arg2
                        | "ContainsAny" => .binaryApp .containsAny arg1 arg2
                        | _ => panic! "unknown op for binary app"
                      | _ => panic "op for binary app is not a string"
                    | false => match (json.getObjVal? "GetAttr").isOk with
                      | true =>
                        let e := (unwrapExcept (json.getObjVal? "GetAttr")).getObjVal? "expr"
                        let wrapped_attr := (unwrapExcept (json.getObjVal? "GetAttr")).getObjVal? "attr"
                        match e.isOk, wrapped_attr.isOk with
                          | true,true => match unwrapExcept wrapped_attr with
                            | Lean.Json.str s => .getAttr (jsonToExpr e) s
                            | _ => panic! "sorry"
                          | _,_ => panic! "sorry"
                      | false => match (json.getObjVal? "HasAttr").isOk with
                        | true =>
                          let e := (unwrapExcept (json.getObjVal? "HasAttr")).getObjVal? "expr"
                          let wrapped_attr := (unwrapExcept (json.getObjVal? "HasAttr")).getObjVal? "attr"
                          match e.isOk, wrapped_attr.isOk with
                            | true,true => match unwrapExcept wrapped_attr with
                              | Lean.Json.str s => .hasAttr (jsonToExpr e) s
                              | _ => panic! "sorry"
                            | _,_ => panic! "sorry"
                        | false => match (json.getObjVal? "Record").isOk with
                          | true =>
                            let e := (unwrapExcept (json.getObjVal? "Record")).getObjVal? "pairs"
                            match e.isOk with
                              | true =>
                                let e := (unwrapExcept e).getArr?
                                match e.isOk with
                                | true =>
                                  let e := Option.get! e.toOption
                                  let kv := arrayToKVPairList e
                                  let v_exprs := List.map jsonToExpr (List.map Except.ok kv.snd)
                                  let k_strs := List.map strNodeToString kv.fst
                                  let er : Expr := .record (List.zip k_strs v_exprs)
                                  er
                                | false => panic! "sorry"
                              | false => panic! "sorry"
                          | false => match (json.getObjVal? "Set").isOk with
                            | true =>
                              let e := (unwrapExcept (json.getObjVal? "Set")).getArr?
                              match e.isOk with
                              | true =>
                                let e := Option.get! e.toOption
                                let es := List.map jsonToExpr (List.map Except.ok e.toList)
                                let exs : Expr := .set es
                                exs
                              | false => panic! "sorry"
                            | false => match (json.getObjVal? "ExtensionFunctionApp").isOk with
                              | true =>
                              let e := (unwrapExcept (json.getObjVal? "ExtensionFunctionApp"))
                              let args := Option.get! ((unwrapExcept (e.getObjVal? "args")).getArr?).toOption
                              let args := List.map (jsonToExpr ∘ Except.ok) args.toList
                              let fn_name := (unwrapExcept ((unwrapExcept (e.getObjVal? "fn_name")).getObjVal? "id")).getStr?
                              match fn_name with
                                | .ok "decimal" => .call .decimal args
                                | .ok "lessThan" => .call .lessThan args
                                | .ok "lessThanOrEqual" => .call .lessThanOrEqual args
                                | .ok "greaterThan" => .call .greaterThan args
                                | .ok "greaterThanOrEqual" => .call .greaterThanOrEqual args
                                | .ok "ip" => .call .ip args
                                | .ok "isIpv4" => .call .isIpv4 args
                                | .ok "isIpv6" => .call .isIpv6 args
                                | .ok "isLoopback" => .call .isLoopback args
                                | .ok "isMulticast" => .call .isMulticast args
                                | .ok "isInRange" => .call .isInRange args
                                | .ok name => panic! "unknown extension function: "++name
                                | .error e => panic! "extension fn name error: "++e
                              | false => panic! json.pretty

partial def exprToValue (expr : Expr) : Value := match expr with
  | Expr.lit p => Value.prim p
  | Expr.record r => Value.record (Map.mk (List.map (λ (a,ex) => (a , exprToValue ex)) r))
  | Expr.set s => Value.set (Set.mk (List.map exprToValue s))
  | Expr.call ty arg => match ty, arg with
    | .decimal, [.lit (.string s)] => match Decimal.decimal s with
      | .some v => .ext (.decimal v)
      | .none => panic! "could not parse decimal"
    | .ip, [.lit (.string s)] => match IPAddr.ip s with
      | .some v => .ext (.ipaddr v)
      | .none => panic! "could not parse ip"
    | _,_ => panic! "unexpected extension function in exprToValue"
  | _ => panic! toString (repr expr)

def jsonToValue (json : Except String Lean.Json) : Value := match json.isOk with
  | false => panic! "sorry"
  | true =>
    (exprToValue ∘ jsonToExpr) json

def jsonToContext (json : Except String Lean.Json) : Map Attr Value := match json.isOk with
  | false => panic! "sorry"
  | true =>
    let json := Option.get! json.toOption
    let pairs_arr := unwrapExcept ((unwrapExcept (json.getObjVal? "expr_kind")).getObjVal? "Record")
    match unwrapExcept (pairs_arr.getObjVal? "pairs") with
      | Lean.Json.arr pairs_json =>
        let kvs := arrayToKVPairList pairs_json
        let keys := List.map strNodeToString kvs.fst
        let vals := List.map (jsonToValue ∘ Except.ok) kvs.snd
        Map.mk (List.zip keys vals)
      | _ => Map.empty

partial def jsonToRequest (json : Except String Lean.Json) : Request := match json.isOk with
  | false => panic! "sorry"
  | true =>
    let json := Option.get! json.toOption
    let json := unwrapExcept (json.getObjVal? "request")
    let principal := jsonToEUID ((unwrapExcept (json.getObjVal? "principal")).getObjVal? "Concrete")
    let action := jsonToEUID ((unwrapExcept (json.getObjVal? "action")).getObjVal? "Concrete")
    let resource := jsonToEUID ((unwrapExcept (json.getObjVal? "resource")).getObjVal? "Concrete")
    let context := (jsonToContext ∘ json.getObjVal?) "context"
    {
      principal := principal,
      action := action,
      resource := resource,
      context := context
    }

def jsonToEntityData (json : Except String Lean.Json) : EntityData := match json.isOk with
| false => panic! "sorry"
| true =>
  let json := Option.get! json.toOption
  let ancestors_json := unwrapExcept (json.getObjVal? "ancestors")
  let ancestors := match ancestors_json with
    | Lean.Json.arr arr => Set.mk (List.map (jsonToEUID ∘ Except.ok) arr.toList)
    | _ => Set.empty
  let attrs_json := unwrapExcept (json.getObjVal? "attrs")
  let attrs := match attrs_json with
  | Lean.Json.obj obj =>
    let pairs := (obj.fold (fun l s j => (s,j) :: l) [])
    let keys := List.map Prod.fst pairs
    let vals := List.map (exprToValue ∘ jsonToExpr ∘ Except.ok ∘ Prod.snd) pairs
    Map.mk (List.zip keys vals)
  | _ => panic! "uh oh"
  {
    ancestors := ancestors,
    attrs := attrs
  }

def jsonToEntities (json : Except String Lean.Json) : Entities := match json.isOk with
| false => panic! "sorry"
| true =>
  let json := Option.get! json.toOption
  let json := unwrapExcept (json.getObjVal? "entities")
  let entities := unwrapExcept (json.getObjVal? "entities")
  match entities with
    | Lean.Json.arr arr =>
      let vs := (arrayToKVPairList arr).snd
      let entityid := List.map (fun x => jsonToEUID (x.getObjVal? "uid")) vs
      let entitydata := List.map (jsonToEntityData ∘ Except.ok) vs
      Map.mk (List.zip entityid entitydata)
    | _ => panic! "sorry"

def strToScopeAny (str : String) : Scope := match str with
| "Any" => .any
| _ => panic! "sorry"

def jsonToArgedScopePR (json : Lean.Json) (isEq : Bool) (isActionScope : Bool) : Scope :=
  let euidJson := if isActionScope then json else unwrapExcept (json.getObjVal? "EUID")
  let euid := jsonToEUID (Except.ok euidJson)
  if isEq then .eq euid else .mem euid

def jsonToActionInAnyListEUID (json : Lean.Json) : List EntityUID := match json.getArr? with
| .ok arr => List.map (jsonToEUID ∘ Except.ok) arr.toList
| .error _ => panic! "sorry"

def jsonToPolicy (json : Except String Lean.Json) : Policy := match json.isOk with
  | false => panic! "sorry"
  | true =>
    let json := Option.get! json.toOption
    let idJson := unwrapExcept (json.getObjVal? "id")
    let id := match idJson.getStr? with
      | .ok str => str
      | _ => panic! "sorry"
    let effectJson := unwrapExcept (json.getObjVal? "effect")
    let effect := match effectJson.getStr? with
      | .ok str => match str with
        | "permit" => Effect.permit
        | "forbid" => Effect.forbid
        | _ => panic! "sorry"
      | .error _ => panic! "sorry"
    let principalConstraintWrapped := unwrapExcept (json.getObjVal? "principal_constraint")
    let principalConstraintJson := unwrapExcept (principalConstraintWrapped.getObjVal? "constraint")
    let principalConstraint := match principalConstraintJson.getStr? with
      | .ok str => .principalScope (strToScopeAny str)
      | .error _ => match principalConstraintJson.getObjVal? "Eq" with
        | .ok eqObj => .principalScope (jsonToArgedScopePR eqObj true false)
        | .error _ => match principalConstraintJson.getObjVal? "In" with
          | .ok inObj => .principalScope (jsonToArgedScopePR inObj false false)
          | _ => panic! "sorry"
    let actionConstraintJson := unwrapExcept (json.getObjVal? "action_constraint")
    let actionConstraint := match actionConstraintJson.getStr? with
      | .ok str => .actionScope (strToScopeAny str)
      | .error _ => match actionConstraintJson.getObjVal? "Eq" with
        | .ok eqObj => .actionScope (jsonToArgedScopePR eqObj true true)
        | .error _ => match actionConstraintJson.getObjVal? "In" with
          | .ok inObj => match inObj.getArr? with
            | .ok _ => .actionInAny (jsonToActionInAnyListEUID inObj)
            | .error _ => .actionScope (jsonToArgedScopePR inObj false true)
          | _ => panic! "sorry"
    let resourceConstraintWrapped := unwrapExcept (json.getObjVal? "resource_constraint")
    let resourceConstraintJson := unwrapExcept (resourceConstraintWrapped.getObjVal? "constraint")
    let resourceConstraint := match resourceConstraintJson.getStr? with
      | .ok str => .resourceScope (strToScopeAny str)
      | .error _ => match resourceConstraintJson.getObjVal? "Eq" with
        | .ok eqObj => .resourceScope (jsonToArgedScopePR eqObj true false)
        | .error _ => match resourceConstraintJson.getObjVal? "In" with
          | .ok inObj => .resourceScope (jsonToArgedScopePR inObj false false)
          | _ => panic! "sorry"
    let condition := jsonToExpr (json.getObjVal? "non_head_constraints")
    {
      id := id
      effect := effect,
      principalScope := principalConstraint,
      resourceScope := resourceConstraint,
      actionScope := actionConstraint,
      condition := condition
    }

-- for now, doesn't include policy templates.
-- a static policy is just a policy template with no blanks.
def jsonToPolicies (json : Except String Lean.Json) : Policies := match json.isOk with
  | false => panic! "sorry"
  | true =>
    let json := Option.get! json.toOption
    let json := unwrapExcept (json.getObjVal? "policies")
    let templates := unwrapExcept (json.getObjVal? "templates")
    match templates.getObj? with
      | .ok obj => List.map (jsonToPolicy ∘ Except.ok ∘ Prod.snd) (obj.fold (fun l s j => (s,j) :: l) [])
      | _ => panic! "sorry"

end DiffTest
