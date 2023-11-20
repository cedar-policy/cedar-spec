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

def jsonToName (json : Lean.Json) : Name :=
  let id := jsonToString (getJsonField json "id")
  let path_json := jsonToArray (getJsonField json "path")
  let path := List.map jsonToString path_json.toList
  {
    id := id,
    path := path
  }

def jsonToEntityType (json : Lean.Json) : EntityType :=
  jsonToName (getJsonField json "Specified")

def jsonToEuid (json : Lean.Json) : EntityUID :=
  let eid := jsonToString (getJsonField json "eid")
  let ty := jsonToEntityType (getJsonField json "ty")
  {
    ty := ty,
    eid := eid
  }

def jsonToPrim (json : Lean.Json) : Prim :=
  let (tag, body) := unpackJsonSum json
  match tag with
  | "Bool" => .bool (jsonToBool body)
  | "Long" => .int (jsonToInt64 body)
  | "String" => .string (jsonToString body)
  | "EntityUID" => .entityUID (jsonToEuid body)
  | tag => panic! s!"jsonToPrim: unknown tag {tag}"

def jsonToVar (json : Lean.Json) : Var :=
  let var := jsonToString json
  match var with
  | "principal" => .principal
  | "action" => .action
  | "resource" => .resource
  | "context" => .context
  | _ => panic! s!"jsonToVar: unknown variable {var}"

def jsonToUnaryOp (json : Lean.Json) : UnaryOp :=
  let op := jsonToString json
  match op with
  | "Not" => .not
  | "Neg" => .neg
  | op => panic! s!"jsonToUnaryOp: unknown operator {op}"

def jsonToPatElem (json : Lean.Json) : PatElem :=
  let (tag, body) := unpackJsonSum json
  match tag with
  | "Wildcard" => .star
  | "Char" => .justChar (jsonToChar body)
  | tag => panic! s!"jsonToPatElem: unsupported tag {tag}"

def jsonToPattern (json : Lean.Json) : Pattern :=
  let elems := jsonToArray json
  List.map jsonToPatElem elems.toList

def jsonToBinaryOp (json : Lean.Json) : BinaryOp :=
  let op := jsonToString json
  match op with
  | "Eq" => .eq
  | "In" => .mem
  | "Less" => .less
  | "LessEq" => .lessEq
  | "Add" => .add
  | "Sub" => .sub
  | "Contains" => .contains
  | "ContainsAll" => .containsAll
  | "ContainsAny" => .containsAny
  | op => panic! s!"jsonToBinaryOp: unknown operator {op}"

def jsonToExtFun (json : Lean.Json) : ExtFun :=
  let xfn := jsonToName json
  match xfn.id with
  | "decimal" => .decimal
  | "lessThan" => .lessThan
  | "lessThanOrEqual" => .lessThanOrEqual
  | "greaterThan" => .greaterThan
  | "greaterThanOrEqual" => .greaterThanOrEqual
  | "ip" => .ip
  | "isIpv4" => .isIpv4
  | "isIpv6" => .isIpv6
  | "isLoopback" => .isLoopback
  | "isMulticast" => .isMulticast
  | "isInRange" => .isInRange
  | xfn => panic! s!"jsonToExtFun: unknown extension function {xfn}"

/-
Defined as partial to avoid writing the proof of termination, which isn't required
since we don't prove correctness of the parser.
-/
partial def jsonToExpr (json : Lean.Json) : Expr :=
  let json := getJsonField json "expr_kind"
  let (tag, body) := unpackJsonSum json
  match tag with
  | "Lit" => .lit (jsonToPrim body)
  | "Var" =>
    let var := jsonToString body
    .var (jsonToVar var)
  | "And" =>
    let lhs := getJsonField body "left"
    let rhs := getJsonField body "right"
    .and (jsonToExpr lhs) (jsonToExpr rhs)
  | "Or" =>
    let lhs := getJsonField body "left"
    let rhs := getJsonField body "right"
    .or (jsonToExpr lhs) (jsonToExpr rhs)
  | "If" =>
    let i := getJsonField body "test_expr"
    let t := getJsonField body "then_expr"
    let e := getJsonField body "else_expr"
    .ite (jsonToExpr i) (jsonToExpr t) (jsonToExpr e)
  | "UnaryApp" =>
    let op := getJsonField body "op"
    let arg := getJsonField body "arg"
    .unaryApp (jsonToUnaryOp op) (jsonToExpr arg)
  | "MulByConst" =>
    let c := getJsonField body "constant"
    let expr := getJsonField body "expr"
    .unaryApp (.mulBy (jsonToInt64 c)) (jsonToExpr expr)
  | "Like" =>
    let pat := getJsonField body "pattern"
    let expr := getJsonField body "expr"
    .unaryApp (.like (jsonToPattern pat)) (jsonToExpr expr)
  | "Is" =>
    let ety := getJsonField body "entity_type"
    let expr := getJsonField body "expr"
    .unaryApp (.is (jsonToName ety)) (jsonToExpr expr)
  | "BinaryApp" =>
    let op := getJsonField body "op"
    let arg1 := getJsonField body "arg1"
    let arg2 := getJsonField body "arg2"
    .binaryApp (jsonToBinaryOp op) (jsonToExpr arg1) (jsonToExpr arg2)
  | "GetAttr" =>
    let e :=  getJsonField body "expr"
    let attr := getJsonField body "attr"
    .getAttr (jsonToExpr e) (jsonToString attr)
  | "HasAttr" =>
    let e :=  getJsonField body "expr"
    let attr := getJsonField body "attr"
    .hasAttr (jsonToExpr e) (jsonToString attr)
  | "Record" =>
    let kvs := jsonObjToKVList body
    .record (List.map (λ (k,v) => (k,jsonToExpr v)) kvs)
  | "Set" =>
    let arr := jsonToArray body
    .set (List.map jsonToExpr arr.toList)
  | "ExtensionFunctionApp" =>
    let args := jsonToArray (getJsonField body "args")
    let fn := getJsonField body "fn_name"
    .call (jsonToExtFun fn) (List.map jsonToExpr args.toList)
  | tag => panic! s!"jsonToExpr: unknown tag {tag}"

def extExprToValue (xfn : ExtFun) (args : List Expr) : Value :=
  match xfn, args with
  | .decimal, [.lit (.string s)] => match Decimal.decimal s with
    | .some v => .ext (.decimal v)
    | .none => panic! s!"exprToValue: failed to parse decimal {s}"
  | .ip, [.lit (.string s)] => match IPAddr.ip s with
    | .some v => .ext (.ipaddr v)
    | .none => panic! s!"exprToValue: failed to parse ip {s}"
  | _,_ => panic! "exprToValue: unexpected extension value\n" ++ toString (repr (Expr.call xfn args))

/-
Convert an expression to a value. This function is used to parse values
that were serialized as expressions in the JSON, so it fails if the
conversion is non-trivial.
-/
partial def exprToValue : Expr → Value
  | Expr.lit p => Value.prim p
  | Expr.record r => Value.record (Map.mk (List.map (λ (k,v) => (k,exprToValue v)) r))
  | Expr.set s => Value.set (Set.mk (List.map exprToValue s))
  | Expr.call xfn args => extExprToValue xfn args
  | expr => panic! "exprToValue: invalid input expression\n" ++ toString (repr expr)

def jsonToValue : Lean.Json → Value := exprToValue ∘ jsonToExpr

def jsonToContext (json : Lean.Json) : Map Attr Value :=
  let value := jsonToValue json
  match value with
  | .record kvs => kvs
  | _ => panic! "jsonToContext: context must be a record\n" ++ toString (repr value)

/-
The "Known" in this function refers to "known" vs. "unknown" entities.
We only need to support the known case here because the Lean does not
support partial evaluation.
-/
def jsonToRequest (json : Lean.Json) : Request :=
  let principal := getJsonField (getJsonField json "principal") "Known"
  let action := getJsonField (getJsonField json "action") "Known"
  let resource := getJsonField (getJsonField json "resource") "Known"
  let context := getJsonField json "context"
  {
    principal := jsonToEuid principal,
    action := jsonToEuid action,
    resource := jsonToEuid resource,
    context := jsonToContext context
  }

def jsonToEntityData (json : Lean.Json) : EntityData :=
  let ancestorsArr := jsonToArray (getJsonField json "ancestors")
  let ancestors := Set.mk (List.map jsonToEuid ancestorsArr.toList)
  let attrsKVs := jsonObjToKVList (getJsonField json "attrs")
  let attrs := Map.mk (List.map (λ (k,v) => (k,jsonToValue v)) attrsKVs)
  {
    ancestors := ancestors,
    attrs := attrs
  }

def jsonToEntities (json : Lean.Json) : Entities :=
  let entities := getJsonField json "entities"
  let kvs := jsonArrayToKVList entities
  Map.mk (List.map (λ (k,v) => (jsonToEuid k, jsonToEntityData v)) kvs)

def jsonToEffect (json : Lean.Json) : Effect :=
  let eff := jsonToString json
  match eff with
  | "permit" => .permit
  | "forbid" => .forbid
  | eff => panic! s!"jsonToEffect: unknown effect {eff}"

/-
Slots not currently supported, but will be added in the future.
-/
def jsonToEuidOrSlot (json : Lean.Json) : EntityUID :=
  let (tag, body) := unpackJsonSum json
  match tag with
  | "EUID" => jsonToEuid body
  | tag => panic! s!"jsonToEuidOrSlot: unknown tag {tag}"

def jsonToScope (json : Lean.Json) : Scope :=
  let (tag, body) := unpackJsonSum json
  match tag with
  | "Any" => .any
  | "In" => .mem (jsonToEuidOrSlot body)
  | "Eq" => .eq (jsonToEuidOrSlot body)
  | "Is" => .is (jsonToName body)
  | "IsIn" =>
    let (ety,e) := jsonToTuple body
    .isMem (jsonToName ety) (jsonToEuidOrSlot e)
  | tag => panic! s!"jsonToScope: unknown tag {tag}"

def jsonToActionScope (json : Lean.Json) : ActionScope :=
  let (tag, body) := unpackJsonSum json
  match tag with
  | "Any" => .actionScope .any
  | "In" =>
    let arr := jsonToArray body
    .actionInAny (List.map jsonToEuid arr.toList)
  | "Eq" => .actionScope (.eq (jsonToEuid body))
  | tag => panic! s!"jsonToActionScope: unknown tag {tag}"

def jsonToPolicy (json : Lean.Json) : Policy :=
  let id := jsonToString (getJsonField json "id")
  let effect := jsonToEffect (getJsonField json "effect")
  let principalConstraint := getJsonField (getJsonField json "principal_constraint") "constraint"
  let actionConstraint := getJsonField json "action_constraint"
  let resourceConstraint := getJsonField (getJsonField json "resource_constraint") "constraint"
  let condition := jsonToExpr (getJsonField json "non_head_constraints")
  {
    id := id
    effect := effect,
    principalScope := .principalScope (jsonToScope principalConstraint),
    resourceScope := .resourceScope (jsonToScope resourceConstraint),
    actionScope := jsonToActionScope actionConstraint,
    condition := condition
  }

/-
For now, `jsonToPolicies` doesn't support policy templates.
A static policy is just a policy template with no blanks.
-/
def jsonToPolicies (json : Lean.Json) : Policies :=
  let templatesKVs := jsonObjToKVList (getJsonField json "templates")
  List.map (λ (_,v) => jsonToPolicy v) templatesKVs

def jsonToPrimType (json : Lean.Json) : CedarType :=
  let tag := jsonToString json
  match tag with
  | "Bool" => .bool .anyBool
  | "Long" => .int
  | "String" => .string
  | tag => panic! s!"jsonToPrimType: unknown tag {tag}"

def jsonToExtType (json : Lean.Json) : ExtType :=
  let xty := jsonToName json
  match xty.id with
  | "ipaddr" => .ipAddr
  | "decimal" => .decimal
  | xty => panic! s!"jsonToExtType: unknown extension type {xty}"

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
  appliesToPricipal : Set EntityType
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
        appliesToPricipal := v.appliesToPricipal,
        appliesToResource := v.appliesToResource,
        ancestors := ancestorMap.find! k,
        context := v.context
      })) acts)

mutual

partial def jsonToQualifiedCedarType (json : Lean.Json) : Qualified CedarType :=
  let attrType := jsonToCedarType (getJsonField json "attrType")
  let isRequired := jsonToBool (getJsonField json "isRequired")
  if isRequired
  then .required attrType
  else .optional attrType

partial def jsonToRecordType (json : Lean.Json) : RecordType :=
  let kvs := jsonObjToKVList json
  Map.mk (List.map (λ (k,v) => (k,jsonToQualifiedCedarType v)) kvs)

partial def jsonToEntityOrRecordType (json : Lean.Json) : CedarType :=
  let (tag,body) := unpackJsonSum json
  match tag with
  | "Record" =>
    let attrs := getJsonField (getJsonField body "attrs") "attrs"
    .record (jsonToRecordType attrs)
  | "Entity" =>
    let lubArr := jsonToArray (getJsonField body "lub_elements")
    let lub := Array.map jsonToName lubArr
    if lub.size == 1
    then .entity lub[0]!
    else panic! "jsonToEntityOrRecordType: expected lub to have exactly one element" ++ json.pretty
  | tag => panic! s!"jsonToEntityOrRecordType: unknown tag {tag}"

partial def jsonToCedarType (json : Lean.Json) : CedarType :=
  let (tag, body) := unpackJsonSum json
  match tag with
    | "Primitive" => jsonToPrimType (getJsonField body "primitiveType")
    | "Set" =>
      let elementType := getJsonField body "elementType"
      .set (jsonToCedarType elementType)
    | "EntityOrRecord" => jsonToEntityOrRecordType body
    | "ExtensionType" =>
      let name := getJsonField body "name"
      .ext (jsonToExtType name)
    | tag => panic! s!"jsonToCedarType: unknown tag {tag}"

partial def jsonToEntityTypeEntry (json : Lean.Json) : JsonEntityTypeStoreEntry :=
  let descendants := jsonToArray (getJsonField json "descendants")
  let attrs := getJsonField (getJsonField json "attributes") "attrs"
  {
    descendants := Set.mk (List.map jsonToName descendants.toList),
    attrs := jsonToRecordType attrs
  }

partial def jsonToSchemaActionEntry (json : Lean.Json) : JsonSchemaActionEntry :=
  let appliesTo := getJsonField json "appliesTo"
  let appliesToPrincipal := jsonToArray (getJsonField appliesTo "principalApplySpec")
  let appliesToResource := jsonToArray (getJsonField appliesTo "resourceApplySpec")
  let descendants := jsonToArray (getJsonField json "descendants")
  let context := getJsonField (getJsonField json "context") "attrs"
  {
    appliesToPricipal := Set.mk (List.map jsonToEntityType appliesToPrincipal.toList),
    appliesToResource := Set.mk (List.map jsonToEntityType appliesToResource.toList),
    descendants := Set.mk (List.map jsonToEuid descendants.toList),
    context := jsonToRecordType context
  }

partial def jsonToSchema (json : Lean.Json) : Schema :=
  let entityTypesKVs := jsonArrayToKVList (getJsonField json "entityTypes")
  let entityTypes := Map.mk (List.map (λ (k,v) => (jsonToName k,jsonToEntityTypeEntry v)) entityTypesKVs)
  let actionsKVs := jsonArrayToKVList (getJsonField json "actionIds")
  let actions := Map.mk (List.map (λ (k,v) => (jsonToEuid k,jsonToSchemaActionEntry v)) actionsKVs)
  {
    ets := invertJsonEntityTypeStore entityTypes,
    acts := invertJsonSchemaActionStore actions
  }

end -- end mutual block

end DiffTest
