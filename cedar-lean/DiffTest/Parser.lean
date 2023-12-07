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

import Std

import Cedar.Data
import Cedar.Spec
import Cedar.Spec.Ext
import Cedar.Validation

import DiffTest.Util

namespace DiffTest

open Cedar.Data
open Cedar.Spec
open Cedar.Spec.Ext
open Cedar.Validation

def jsonToName (json : Lean.Json) : ParseResult Name := do
  let id ← getJsonField json "id" >>= jsonToString
  let path_json ← getJsonField json "path" >>= jsonToArray
  let path ← List.mapM jsonToString path_json.toList
  .ok {
    id := id,
    path := path
  }

def jsonToEntityType (json : Lean.Json) : ParseResult EntityType :=
  getJsonField json "Specified" >>= jsonToName

def jsonToEuid (json : Lean.Json) : ParseResult EntityUID := do
  let eid ← getJsonField json "eid" >>= jsonToString
  let ty ← getJsonField json "ty" >>= jsonToEntityType
  .ok {
    ty := ty,
    eid := eid
  }

def jsonToPrim (json : Lean.Json) : ParseResult Prim := do
  let (tag, body) ← unpackJsonSum json
  match tag with
  | "Bool" => do
    let b ←  jsonToBool body
    .ok (.bool b)
  | "Long" => do
    let i ← jsonToInt64 body
    .ok (.int i)
  | "String" =>
    let s ← jsonToString body
    .ok (.string s)
  | "EntityUID" =>
    let e ← jsonToEuid body
    .ok (.entityUID e)
  | tag => .error s!"jsonToPrim: unknown tag {tag}"

def jsonToVar (json : Lean.Json) : ParseResult Var := do
  let var ← jsonToString json
  match var with
  | "principal" => .ok .principal
  | "action" => .ok .action
  | "resource" => .ok .resource
  | "context" => .ok .context
  | _ => .error s!"jsonToVar: unknown variable {var}"

def jsonToUnaryOp (json : Lean.Json) : ParseResult UnaryOp := do
  let op ← jsonToString json
  match op with
  | "Not" => .ok .not
  | "Neg" => .ok .neg
  | op => .error s!"jsonToUnaryOp: unknown operator {op}"

def jsonToPatElem (json : Lean.Json) : ParseResult PatElem := do
  let (tag, body) ← unpackJsonSum json
  match tag with
  | "Wildcard" => .ok .star
  | "Char" => do
    let c ← jsonToChar body
    .ok (.justChar c)
  | tag => .error s!"jsonToPatElem: unsupported tag {tag}"

def jsonToPattern (json : Lean.Json) : ParseResult Pattern := do
  let elems ← jsonToArray json
  List.mapM jsonToPatElem elems.toList

def jsonToBinaryOp (json : Lean.Json) : ParseResult BinaryOp := do
  let op ← jsonToString json
  match op with
  | "Eq" => .ok .eq
  | "In" => .ok .mem
  | "Less" => .ok .less
  | "LessEq" => .ok .lessEq
  | "Add" => .ok .add
  | "Sub" => .ok .sub
  | "Contains" => .ok .contains
  | "ContainsAll" => .ok .containsAll
  | "ContainsAny" => .ok .containsAny
  | op => .error s!"jsonToBinaryOp: unknown operator {op}"

def jsonToExtFun (json : Lean.Json) : ParseResult ExtFun := do
  let xfn ← jsonToName json
  match xfn.id with
  | "decimal" => .ok .decimal
  | "lessThan" => .ok .lessThan
  | "lessThanOrEqual" => .ok .lessThanOrEqual
  | "greaterThan" => .ok .greaterThan
  | "greaterThanOrEqual" => .ok .greaterThanOrEqual
  | "ip" => .ok .ip
  | "isIpv4" => .ok .isIpv4
  | "isIpv6" => .ok .isIpv6
  | "isLoopback" => .ok .isLoopback
  | "isMulticast" => .ok .isMulticast
  | "isInRange" => .ok .isInRange
  | xfn => .error s!"jsonToExtFun: unknown extension function {xfn}"

/-
Defined as partial to avoid writing the proof of termination, which isn't required
since we don't prove correctness of the parser.
-/
partial def jsonToExpr (json : Lean.Json) : ParseResult Expr := do
  let json ← getJsonField json "expr_kind"
  let (tag, body) ← unpackJsonSum json
  match tag with
  | "Lit" => do
    let prim ← jsonToPrim body
    .ok (.lit prim)
  | "Var" => do
    let var ← jsonToVar body
    .ok (.var var)
  | "And" => do
    let lhs ← getJsonField body "left" >>= jsonToExpr
    let rhs ← getJsonField body "right" >>= jsonToExpr
    .ok (.and lhs rhs)
  | "Or" => do
    let lhs ← getJsonField body "left" >>= jsonToExpr
    let rhs ← getJsonField body "right" >>= jsonToExpr
    .ok (.or lhs rhs)
  | "If" => do
    let i ← getJsonField body "test_expr" >>= jsonToExpr
    let t ← getJsonField body "then_expr" >>= jsonToExpr
    let e ← getJsonField body "else_expr" >>= jsonToExpr
    .ok (.ite i t e)
  | "UnaryApp" => do
    let op ← getJsonField body "op" >>= jsonToUnaryOp
    let arg ← getJsonField body "arg" >>= jsonToExpr
    .ok (.unaryApp op arg)
  | "MulByConst" => do
    let c ← getJsonField body "constant" >>= jsonToInt64
    let arg ← getJsonField body "arg" >>= jsonToExpr
    .ok (.unaryApp (.mulBy c) arg)
  | "Like" => do
    let pat ← getJsonField body "pattern" >>= jsonToPattern
    let expr ← getJsonField body "expr" >>= jsonToExpr
    .ok (.unaryApp (.like pat) expr)
  | "Is" => do
    let ety ← getJsonField body "entity_type" >>= jsonToName
    let expr ← getJsonField body "expr" >>= jsonToExpr
    .ok (.unaryApp (.is ety) expr)
  | "BinaryApp" => do
    let op ← getJsonField body "op" >>= jsonToBinaryOp
    let arg1 ← getJsonField body "arg1" >>= jsonToExpr
    let arg2 ← getJsonField body "arg2" >>= jsonToExpr
    .ok (.binaryApp op arg1 arg2)
  | "GetAttr" => do
    let e ← getJsonField body "expr" >>= jsonToExpr
    let attr ← getJsonField body "attr" >>= jsonToString
    .ok (.getAttr e attr)
  | "HasAttr" => do
    let e ← getJsonField body "expr" >>= jsonToExpr
    let attr ← getJsonField body "attr" >>= jsonToString
    .ok (.hasAttr e attr)
  | "Record" => do
    let kvs_json ← jsonObjToKVList body
    let kvs ← List.mapM (λ (k,v) => jsonToExpr v >>= λ v => .ok (k,v)) kvs_json
    .ok (.record kvs)
  | "Set" => do
    let arr_json ← jsonToArray body
    let arr ← List.mapM jsonToExpr arr_json.toList
    .ok (.set arr)
  | "ExtensionFunctionApp" => do
    let fn ← getJsonField body "fn_name" >>= jsonToExtFun
    let args_json ← getJsonField body "args" >>= jsonToArray
    let args ← List.mapM jsonToExpr args_json.toList
    .ok (.call fn args)
  | tag => .error s!"jsonToExpr: unknown tag {tag}"

def extExprToValue (xfn : ExtFun) (args : List Expr) : ParseResult Value :=
  match xfn, args with
  | .decimal, [.lit (.string s)] => match Decimal.decimal s with
    | .some v => .ok (.ext (.decimal v))
    | .none => .error s!"exprToValue: failed to parse decimal {s}"
  | .ip, [.lit (.string s)] => match IPAddr.ip s with
    | .some v => .ok (.ext (.ipaddr v))
    | .none => .error s!"exprToValue: failed to parse ip {s}"
  | _,_ => .error ("exprToValue: unexpected extension value\n" ++ toString (repr (Expr.call xfn args)))

/-
Convert an expression to a value. This function is used to parse values
that were serialized as expressions in the JSON, so it fails if the
conversion is non-trivial.
-/
partial def exprToValue : Expr → ParseResult Value
  | Expr.lit p => .ok (Value.prim p)
  | Expr.record r => do
    let kvs ← List.mapM (λ (k,v) => exprToValue v >>= λ v => .ok (k,v)) r
    .ok (Value.record (Map.mk kvs))
  | Expr.set s => do
    let arr ← List.mapM exprToValue s
    .ok (Value.set (Set.mk arr))
  | Expr.call xfn args => extExprToValue xfn args
  | expr => .error ("exprToValue: invalid input expression\n" ++ toString (repr expr))

def jsonToValue (json : Lean.Json) : ParseResult Value :=
  jsonToExpr json >>= exprToValue

def jsonToContext (json : Lean.Json) : ParseResult (Map Attr Value) := do
  let value ← jsonToValue json
  match value with
  | .record kvs => .ok kvs
  | _ => .error ("jsonToContext: context must be a record\n" ++ toString (repr value))

/-
The "Known" in this function refers to "known" vs. "unknown" entities.
We only need to support the known case here because the Lean does not
support partial evaluation.
-/
def jsonToRequest (json : Lean.Json) : ParseResult Request := do
  let principal ← getJsonField json "principal" >>= (getJsonField · "Known") >>= jsonToEuid
  let action ← getJsonField json "action" >>= (getJsonField · "Known") >>= jsonToEuid
  let resource ← getJsonField json "resource" >>= (getJsonField · "Known") >>= jsonToEuid
  let context ← getJsonField json "context" >>= jsonToContext
  .ok {
    principal := principal,
    action := action,
    resource := resource,
    context := context
  }

def jsonToEntityData (json : Lean.Json) : ParseResult EntityData := do
  let ancestorsArr ← getJsonField json "ancestors" >>= jsonToArray
  let ancestors ← List.mapM jsonToEuid ancestorsArr.toList
  let attrsKVs ← getJsonField json "attrs" >>= jsonObjToKVList
  let attrs ← List.mapM (λ (k,v) => jsonToValue v >>= λ v => .ok (k,v)) attrsKVs
  .ok {
    ancestors := Set.mk ancestors,
    attrs := Map.mk attrs
  }

def jsonToEntities (json : Lean.Json) : ParseResult Entities := do
  let entities ← getJsonField json "entities"
  let kvs_json ← jsonArrayToKVList entities
  let kvs ← List.mapM (λ (k,v) => jsonToEuid k >>= λ k => jsonToEntityData v >>= λ v => .ok (k, v)) kvs_json
  .ok (Map.mk kvs)

def jsonToEffect (json : Lean.Json) : ParseResult Effect := do
  let eff ← jsonToString json
  match eff with
  | "permit" => .ok .permit
  | "forbid" => .ok .forbid
  | eff => .error s!"jsonToEffect: unknown effect {eff}"

/-
Slots not currently supported, but will be added in the future.
-/
def jsonToEuidOrSlot (json : Lean.Json) : ParseResult EntityUID := do
  let (tag, body) ← unpackJsonSum json
  match tag with
  | "EUID" => jsonToEuid body
  | tag => .error s!"jsonToEuidOrSlot: unknown tag {tag}"

def jsonToScope (json : Lean.Json) : ParseResult Scope := do
  let (tag, body) ← unpackJsonSum json
  match tag with
  | "Any" => .ok .any
  | "In" => do
    let euidOrSlot ← jsonToEuidOrSlot body
    .ok (.mem euidOrSlot)
  | "Eq" => do
    let euidOrSlot ← jsonToEuidOrSlot body
    .ok (.eq euidOrSlot)
  | "Is" => do
    let name ← jsonToName body
    .ok (.is name)
  | "IsIn" => do
    let (ety,e) ← jsonToTuple body
    let name ← jsonToName ety
    let euidOrSlot ← jsonToEuidOrSlot e
    .ok (.isMem name euidOrSlot)
  | tag => .error s!"jsonToScope: unknown tag {tag}"

def jsonToActionScope (json : Lean.Json) : ParseResult ActionScope := do
  let (tag, body) ← unpackJsonSum json
  match tag with
  | "Any" => .ok (.actionScope .any)
  | "In" => do
    let arr_json ← jsonToArray body
    let arr ← List.mapM jsonToEuid arr_json.toList
    .ok (.actionInAny arr)
  | "Eq" =>
    let euid ← jsonToEuid body
    .ok (.actionScope (.eq euid))
  | tag => .error s!"jsonToActionScope: unknown tag {tag}"

def jsonToPolicy (json : Lean.Json) : ParseResult Policy := do
  let id ← getJsonField json "id" >>= jsonToString
  let effect ← getJsonField json "effect" >>= jsonToEffect
  let principalConstraint ← getJsonField json "principal_constraint" >>= (getJsonField · "constraint") >>= jsonToScope
  let actionConstraint ← getJsonField json "action_constraint" >>= jsonToActionScope
  let resourceConstraint ← getJsonField json "resource_constraint" >>= (getJsonField · "constraint") >>= jsonToScope
  let condition ← getJsonField json "non_head_constraints" >>= jsonToExpr
  .ok {
    id := id
    effect := effect,
    principalScope := .principalScope principalConstraint,
    resourceScope := .resourceScope resourceConstraint,
    actionScope := actionConstraint,
    condition := condition
  }

/-
For now, `jsonToPolicies` doesn't support policy templates.
A static policy is just a policy template with no blanks.
-/
def jsonToPolicies (json : Lean.Json) : ParseResult Policies := do
  let templatesKVs ← getJsonField json "templates" >>= jsonObjToKVList
  List.mapM (λ (_,v) => jsonToPolicy v) templatesKVs

def jsonToPrimType (json : Lean.Json) : ParseResult CedarType := do
  let tag ← jsonToString json
  match tag with
  | "Bool" => .ok (.bool .anyBool)
  | "Long" => .ok .int
  | "String" => .ok .string
  | tag => .error s!"jsonToPrimType: unknown tag {tag}"

def jsonToExtType (json : Lean.Json) : ParseResult ExtType := do
  let xty ← jsonToName json
  match xty.id with
  | "ipaddr" => .ok .ipAddr
  | "decimal" => .ok .decimal
  | xty => .error s!"jsonToExtType: unknown extension type {xty}"

/-
The Rust data types store _descendant_ information for the entity type store
and action store, but _ancestor_ information for the entity store. The Lean
formalization standardizes on ancestor information.

The definitions and utility functions below are used to convert the descendant
representation to the ancestor representation.
-/
def findInMapValues [LT α] [BEq α] [DecidableLT α] (m : Map α (Set α)) (k₁ : α) : Set α :=
  let setOfSets := List.map (λ (k₂,v) => if v.contains k₁ then Set.singleton k₂ else Set.empty) m.toList
  setOfSets.foldl (λ acc v => acc.union v) Set.empty

def descendantsToAncestors [LT α] [BEq α] [DecidableLT α] (descendants : Map α (Set α)) : Map α (Set α) :=
  Map.mk (List.map
    (λ (k,_) => (k, findInMapValues descendants k)) descendants.toList)

structure JsonEntityTypeStoreEntry where
  descendants : Cedar.Data.Set EntityType
  attrs : RecordType

abbrev JsonEntityTypeStore := Map EntityType JsonEntityTypeStoreEntry

structure JsonSchemaActionEntry where
  appliesToPrincipal : Set EntityType
  appliesToResource : Set EntityType
  descendants : Set EntityUID
  context : RecordType

abbrev JsonSchemaActionStore := Map EntityUID JsonSchemaActionEntry

def invertJsonEntityTypeStore (ets : JsonEntityTypeStore) : EntityTypeStore :=
  let ets := ets.toList
  let descendantMap := Map.mk (List.map (λ (k,v) => (k,v.descendants)) ets)
  let ancestorMap := descendantsToAncestors descendantMap
  Map.mk (List.map
    (λ (k,v) => (k,
      {
        ancestors := ancestorMap.find! k,
        attrs := v.attrs
      })) ets)

def invertJsonSchemaActionStore (acts : JsonSchemaActionStore) : SchemaActionStore :=
  let acts := acts.toList
  let descendantMap := Map.mk (List.map (λ (k,v) => (k,v.descendants)) acts)
  let ancestorMap := descendantsToAncestors descendantMap
  Map.mk (List.map
    (λ (k,v) => (k,
      {
        appliesToPrincipal := v.appliesToPrincipal,
        appliesToResource := v.appliesToResource,
        ancestors := ancestorMap.find! k,
        context := v.context
      })) acts)

mutual

partial def jsonToQualifiedCedarType (json : Lean.Json) : ParseResult (Qualified CedarType) := do
  let attrType ← getJsonField json "attrType" >>= jsonToCedarType
  let isRequired ← getJsonField json "isRequired" >>= jsonToBool
  if isRequired
  then .ok (.required attrType)
  else .ok (.optional attrType)

partial def jsonToRecordType (json : Lean.Json) : ParseResult RecordType := do
  let kvs_json ← jsonObjToKVList json
  let kvs ←  List.mapM (λ (k,v) => jsonToQualifiedCedarType v >>= λ v => .ok (k,v)) kvs_json
  .ok (Map.mk kvs)

partial def jsonToEntityOrRecordType (json : Lean.Json) : ParseResult CedarType := do
  let (tag,body) ← unpackJsonSum json
  match tag with
  | "Record" => do
    let attrs ← getJsonField body "attrs" >>= (getJsonField · "attrs") >>= jsonToRecordType
    .ok (.record attrs)
  | "Entity" => do
    let lubArr ← getJsonField body "lub_elements" >>= jsonToArray
    let lub ← Array.mapM jsonToName lubArr
    if lub.size == 1
    then .ok (.entity lub[0]!)
    else .error s!"jsonToEntityOrRecordType: expected lub to have exactly one element¬{json.pretty}"
  | tag => .error s!"jsonToEntityOrRecordType: unknown tag {tag}"

partial def jsonToCedarType (json : Lean.Json) : ParseResult CedarType := do
  let (tag, body) ← unpackJsonSum json
  match tag with
    | "Primitive" => getJsonField body "primitiveType" >>= jsonToPrimType
    | "Set" => do
      let elementType ← getJsonField body "elementType" >>= jsonToCedarType
      .ok (.set elementType)
    | "EntityOrRecord" => jsonToEntityOrRecordType body
    | "ExtensionType" => do
      let name ← getJsonField body "name" >>= jsonToExtType
      .ok (.ext name)
    | tag => .error s!"jsonToCedarType: unknown tag {tag}"

partial def jsonToEntityTypeEntry (json : Lean.Json) : ParseResult JsonEntityTypeStoreEntry := do
  let descendants_json ← getJsonField json "descendants" >>= jsonToArray
  let descendants ← List.mapM jsonToName descendants_json.toList
  let attrs ← getJsonField json "attributes" >>= (getJsonField · "attrs") >>= jsonToRecordType
  .ok {
    descendants := Set.mk descendants,
    attrs := attrs
  }

partial def jsonToSchemaActionEntry (json : Lean.Json) : ParseResult JsonSchemaActionEntry := do
  let appliesTo ← getJsonField json "appliesTo"
  let appliesToPrincipal_json ← getJsonField appliesTo "principalApplySpec" >>= jsonToArray
  let appliesToPrincipal ← List.mapM jsonToEntityType appliesToPrincipal_json.toList
  let appliesToResource_json ← getJsonField appliesTo "resourceApplySpec" >>= jsonToArray
  let appliesToResource ← List.mapM jsonToEntityType appliesToResource_json.toList
  let descendants_json ← getJsonField json "descendants" >>= jsonToArray
  let descendants ← List.mapM jsonToEuid descendants_json.toList
  let context ← getJsonField json "context" >>= jsonToCedarType
  match context with
  | .record rty =>
    .ok {
      appliesToPrincipal := Set.mk appliesToPrincipal,
      appliesToResource := Set.mk appliesToResource,
      descendants := Set.mk descendants,
      context := rty
    }
  | _ => .error "jsonToSchemaActionEntry: context should be record-typed"

partial def jsonToSchema (json : Lean.Json) : ParseResult Schema := do
  let entityTypesKVs ← getJsonField json "entityTypes" >>= jsonArrayToKVList
  let entityTypes ← List.mapM (λ (k,v) => jsonToName k >>= λ k => jsonToEntityTypeEntry v >>= λ v => .ok (k,v)) entityTypesKVs
  let actionsKVs ← getJsonField json "actionIds" >>= jsonArrayToKVList
  let actions ← List.mapM (λ (k,v) => jsonToEuid k >>= λ k => jsonToSchemaActionEntry v >>= λ v => .ok (k,v)) actionsKVs
  .ok {
    ets := invertJsonEntityTypeStore (Map.mk entityTypes),
    acts := invertJsonSchemaActionStore (Map.mk actions)
  }

end -- end mutual block

end DiffTest
