/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

include "base.dfy"
include "ext.dfy"

// Datatypes used by the reference (definitional) Cedar authorization
// engine.

module def.core {
  import opened base
  import ext

  // ----- Pattern literals ----- //

  // Represents an element in a pattern literal (i.e., the RHS of the `like` operator)
  // A pattern element is either a char literal or a wildcard star.
  datatype PatElem = Star | JustChar(char)

  type Pattern = seq<PatElem>

  // ----- Values ----- //

  datatype EntityType = EntityType(id: Name) {
    // CedarCore has an EntityType with "concrete" and "unspecified"
    // alternatives, but making that change right now would break too much of
    // CedarDafny. Instead, in places where we need to handle "unspecified
    // entities" specially, we represent them using this sentinel type name. In
    // places where we can get away with treating unspecified entities the same
    // as others, we do.
    static const UNSPECIFIED := EntityType(Name.fromStr("<Unspecified>"))
  }

  datatype EntityUID = EntityUID(ty: EntityType, eid: string)

  // We specify field names in Primitive and Value for convenience of extracting
  // a value after calling typeCheck with a single expected type.
  datatype Primitive =
    Bool(b: bool) |
    // TODO: We probably want to rename the constructor to `Long` and the field
    // to `l`. This will cause a lot of churn, so to reduce distraction when
    // reviewing my branch, I'm not doing it yet.
    Int(i: i64) |
    String(s: string) |
    EntityUID(uid: EntityUID)

  datatype Value =
    Primitive(primitive: Primitive) |
    Set(s: set<Value>) |
    Record(record: Record) |
    Extension(ex: ext.Value)
  {
    // Conveniences to reduce boilerplate.
    static function Bool(b: bool): Value {
      Primitive(Primitive.Bool(b))
    }
    static const TRUE := Bool(true)
    static const FALSE := Bool(false)

    static function Int(i: i64): Value {
      Primitive(Primitive.Int(i))
    }

    static function String(s: string): Value {
      Primitive(Primitive.String(s))
    }

    static function EntityUID(uid: EntityUID): Value {
      Primitive(Primitive.EntityUID(uid))
    }

    static function Ext(v: ext.Value): Value {
      Value.Extension(v)
    }

    // Dynamic conversion from a Value to a wrapped type.
    // We're making these conversions static so that we can
    // use them as first-class functions.
    static function asBool(v: Value): Result<bool> {
      match v {
        case Primitive(Bool(b)) => Ok(b)
        case _ => Err(TypeError)
      }
    }

    static function asInt(v: Value): Result<i64> {
      match v {
        case Primitive(Int(i)) => Ok(i)
        case _ => Err(TypeError)
      }
    }

    static function asString(v: Value): Result<string> {
      match v {
        case Primitive(String(s)) => Ok(s)
        case _ => Err(TypeError)
      }
    }

    static function asEntity(v: Value): Result<EntityUID> {
      match v {
        case Primitive(EntityUID(e)) => Ok(e)
        case _ => Err(TypeError)
      }
    }

    static function asSet(v: Value): Result<set<Value>> {
      match v {
        case Set(s) => Ok(s)
        case _ => Err(TypeError)
      }
    }

    static function asRecord(v: Value): Result<Record> {
      match v {
        case Record(r) => Ok(r)
        case _ => Err(TypeError)
      }
    }

    static function asExt(v: Value): Result<ext.Value> {
      match v {
        case Extension(e) => Ok(e)
        case _ => Err(TypeError)
      }
    }
  }

  type Attr = string
  type Record = map<Attr, Value>

  const coerce: ext.fun.Coercions<ext.Value, Value> :=
    ext.fun.Coercions(
      Coerce(Value.Bool,   Value.asBool),
      Coerce(Value.Int,    Value.asInt),
      Coerce(Value.String, Value.asString),
      Coerce(Value.Ext,    Value.asExt))

  const extFuns: map<Name, ext.fun.ExtFun<Value>> := ext.register(coerce)

  // ----- Expressions ----- //

  datatype Var = Principal | Action | Resource | Context

  datatype UnaryOp =
    Not |
    Neg | MulBy(i: i64) |
    Like(p: Pattern)

  datatype BinaryOp =
    Eq | In |
    Less | LessEq | Add | Sub |
    Contains | ContainsAll | ContainsAny

  datatype Expr =
    PrimitiveLit(Primitive) |
    Var(Var) |
    If(Expr, Expr, Expr) |
    And(Expr, Expr) | // shortcircuiting &&
    Or(Expr, Expr)  | // shortcircuiting ||
    UnaryApp(UnaryOp, Expr) |
    BinaryApp(BinaryOp, Expr, Expr) |
    GetAttr(Expr, Attr) |
    HasAttr(Expr, Attr) |
    Set(seq<Expr>) |
    Record(fvs: seq<(Attr, Expr)>) |
    Call(name: Name, args: seq<Expr>)

  // ----- Policies, requests, stores, and responses ----- //

  datatype Effect = Permit | Forbid

  datatype PolicyID = PolicyID(id: string)

  datatype Policy = Policy(
    effect: Effect,
    principalScope: PrincipalScope,
    actionScope: ActionScope,
    resourceScope: ResourceScope,
    condition: Expr)
  {
    function toExpr(): Expr {
      Expr.And(
        principalScope.toExpr(),
        Expr.And(
          actionScope.toExpr(),
          Expr.And(
            resourceScope.toExpr(),
            condition)))
    }
  }

  datatype PrincipalScope = PrincipalScope(scope: Scope)
  {
    function toExpr(): Expr {
      scope.toExpr(Var.Principal)
    }
  }

  datatype ResourceScope = ResourceScope(scope: Scope)
  {
    function toExpr(): Expr {
      scope.toExpr(Var.Resource)
    }
  }

  datatype ActionScope = ActionScope(Scope) | ActionInAny(seq<EntityUID>)
  {
    function toExpr(): Expr {
      match this {
        case ActionScope(scope) => scope.toExpr(Var.Action)
        case ActionInAny(es) =>
          var exprs := seq(|es|,
                       i requires 0 <= i < |es| =>
                         PrimitiveLit(Primitive.EntityUID(es[i])));
          BinaryApp(BinaryOp.In, Var(Var.Action), Expr.Set(exprs))
      }
    }
  }

  datatype Scope = Any | Eq(entity: EntityUID) | In(entity: EntityUID)
  {
    function toExpr(v: Var): Expr {
      match this {
        case Any   => PrimitiveLit(Primitive.Bool(true))
        case Eq(e) => BinaryApp(BinaryOp.Eq, Var(v), PrimitiveLit(Primitive.EntityUID(e)))
        case In(e) => BinaryApp(BinaryOp.In, Var(v), PrimitiveLit(Primitive.EntityUID(e)))
      }
    }
  }

  datatype Request =
    Request(principal: EntityUID,
            action: EntityUID,
            resource: EntityUID,
            context: Record)

  datatype EntityData = EntityData(attrs: Record, ancestors: set<EntityUID>)

  datatype EntityStore = EntityStore(
    entities: map<EntityUID, EntityData>)
  {
    // Can also be used just to test whether an entity exists in the store.
    function getEntityAttrs(uid: EntityUID): base.Result<Record> {
      if uid in entities.Keys then
        Ok(entities[uid].attrs)
      else
        Err(EntityDoesNotExist)
    }

    predicate entityIn(child: EntityUID, ancestor: EntityUID)
      requires child in entities.Keys
    {
      ancestor in entities[child].ancestors
    }
  }

  // Note: PolicyStore previously had an `overrides` field and might have it
  // again in the future. To reduce code churn, we aren't collapsing the
  // datatype to a type alias.
  datatype PolicyStore = PolicyStore(
    policies: map<PolicyID, Policy>)

  datatype Store = Store(entities: EntityStore, policies: PolicyStore)

  // ----- Authorization response ----- //

  datatype Response = Response(decision: Decision, policies: set<PolicyID>)

  datatype Decision = Allow | Deny
}
