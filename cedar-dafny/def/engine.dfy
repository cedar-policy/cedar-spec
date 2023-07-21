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
include "core.dfy"
include "wildcard.dfy"

module def.engine {
  import opened base
  import opened core
  import opened wildcard

  datatype Authorizer = Authorizer(request: Request, store: Store) {

    // Only isAuthorized is considered a public API, but we have to expose the
    // intermediate steps in order to write intermediate tests so that we can
    // write a test for isAuthorized without exceeding the limit on how much
    // Dafny will evaluate in one step.

    function evaluator(): Evaluator {
      Evaluator(request, store.entities)
    }

    function evaluate(pid: PolicyID): Result<Value>
      requires pid in store.policies.policies
    {
      evaluator().interpret(store.policies.policies[pid].toExpr())
    }

    predicate satisfied(pid: PolicyID)
      requires pid in store.policies.policies
    {
      evaluate(pid) == Ok(Value.TRUE)
    }

    function satisfiedPolicies(): set<PolicyID> {
      set pid | pid in store.policies.policies.Keys &&
                satisfied(pid)
    }

    function forbids(): set<PolicyID> {
      set pid | pid in satisfiedPolicies() &&
                store.policies.policies[pid].effect == Forbid
    }

    // NOTE: Now that overrides have been removed for the time being, `permits`
    // has been redefined to return _all_ permit policies that are in force, not
    // only those that override all forbid policies in force.  This is
    // consistent with the definitions in the version of the language
    // specification without overrides.
    function permits(): set<PolicyID> {
      set pid | pid in satisfiedPolicies() &&
                store.policies.policies[pid].effect == Permit
    }

    function isAuthorized(): Response {
      var f := forbids();
      var p := permits();
      if f == {} && p != {} then
        Response(Allow, p)
      else
        Response(Deny, f)
    }
  }

  datatype Evaluator = Evaluator(request: Request, store: EntityStore) {

    function interpret(expr: Expr): Result<Value> {
      match expr {
        case PrimitiveLit(p) => Ok(Primitive(p))
        case Var(v) =>
          match v {
            case Principal => Ok(Value.EntityUID(request.principal))
            case Action => Ok(Value.EntityUID(request.action))
            case Resource => Ok(Value.EntityUID(request.resource))
            case Context => Ok(Value.Record(request.context))
          }
        case If(e_cond, e_true, e_false) =>
          var v_cond :- interpret(e_cond);
          var b_cond :- Value.asBool(v_cond);
          if b_cond then interpret(e_true) else interpret(e_false)
        case And(left, right) =>
          interpretShortcircuit(expr, left, right, false)
        case Or(left, right) =>
          interpretShortcircuit(expr, left, right, true)
        case UnaryApp(op, e) =>
          var v :- interpret(e);
          applyUnaryOp(op, v)
        case BinaryApp(op, e1, e2) =>
          var v1 :- interpret(e1);
          var v2 :- interpret(e2);
          applyBinaryOp(op, v1, v2)
        case GetAttr(e, a) =>
          var v :- interpret(e);
          var r :- expectRecordDerefEntity(v, false);
          if a in r.Keys then Ok(r[a]) else Err(AttrDoesNotExist)
        case HasAttr(e, a) =>
          var v :- interpret(e);
          var r :- expectRecordDerefEntity(v, true);
          Ok(Value.Bool(a in r.Keys))
        case Set(es) =>
          var vs :- interpretSet(es);
          Ok(Value.Set(vs))
        case Record(es) =>
          var fvs :- interpretRecord(es);
          Ok(Value.Record(fvs))
        case Call(name, es) =>
          var args :- interpretList(es);
          applyExtFun(name, args)
      }
    }

    static function applyExtFun(name: Name, args: seq<Value>): Result<Value> {
      if name in extFuns.Keys
      then
        var fn := extFuns[name];
        fn.fun(args)
      else Err(NoSuchFunctionError)
    }

    // We allow repeated keys in Record literal definitions, and take the last
    // value given for a field. For example, { a: 1, b: 2, a: 3 } evaluates to
    // the record {b: 2, a: 3 }. We do not throw an error in the case of
    // repeated field IDs, this allows for duplicate keys in map literals
    function interpretRecord(es: seq<(Attr,Expr)>): Result<map<Attr, Value>> {
      if es == [] then
        Ok(map[])
      else
        var k := es[0].0;
        var v :- interpret(es[0].1);
        var m :- interpretRecord(es[1..]);
        if k in m.Keys then // If the same field is repeated later in the record,
          Ok(m)             // we give that occurrence priority and ignore this one.
        else
          Ok(m[k := v])
    }

    // We allow repeated elements in Set literal definitions, and drop
    // duplicates. For example, { 1, 2, 3, 2 } evaluates to the Set {1, 2, 3}.
    function interpretSet(es: seq<Expr>): Result<set<Value>> {
      if es == [] then
        Ok({})
      else
        var head_v :- interpret(es[0]);
        var tail_vs :- interpretSet(es[1..]);
        Ok({head_v} + tail_vs)
    }

    function interpretList(es: seq<Expr>): Result<seq<Value>> {
      if es == [] then
        Ok([])
      else
        var head_v :- interpret(es[0]);
        var tail_vs :- interpretList(es[1..]);
        Ok([head_v] + tail_vs)
    }

    // Evaluates each expression in order. If left returns short or errors, then
    // stop and return short or error. Otherwise, returns the result of right.
    // This is used to implement && with short = false and || with short = true.
    // The ghost variable expr is required to pass the termination check.
    function interpretShortcircuit(ghost expr: Expr, left: Expr, right: Expr, short: bool): Result<Value>
      requires left < expr && right < expr
    {
      var l :- interpret(left);
      var b :- Value.asBool(l);
      if b == short
      then Ok(l)
      else
        var r :- interpret(right);
        var _ :- Value.asBool(r);
        Ok(r)
    }

    function expectRecordDerefEntity(v: Value, treatMissingAsEmpty: bool): Result<Record> {
      if v.Record?
      then Ok(v.record)
      else
        var uid :- Value.asEntity(v);
        var res := store.getEntityAttrs(uid);
        if res.Err? && treatMissingAsEmpty then Ok(map[]) else res
    }

    function applyUnaryOp(uop: UnaryOp, x: Value): Result<Value> {
      match uop {
        case Not =>
          var b :- Value.asBool(x);
          Ok(Value.Bool(!b))
        case Neg =>
          applyIntUnaryOp(a => -a, x)
        case MulBy(factor) =>
          applyIntUnaryOp(a => factor * a, x)
        case Like(p) =>
          var s :- Value.asString(x);
          Ok(Value.Bool(wildcardMatch(s, p)))
      }
    }

    function applyIntUnaryOp(f: int -> int, x: Value): Result<Value> {
      var i :- Value.asInt(x);
      Ok(Value.Int(f(i)))
    }

    function applyIntBinaryOp(f: (int, int) -> int, x: Value, y: Value): Result<Value> {
      var xi :- Value.asInt(x);
      var yi :- Value.asInt(y);
      Ok(Value.Int(f(xi, yi)))
    }

    function applyIntBinaryPred(f: (int, int) -> bool, x: Value, y: Value): Result<Value> {
      var xi :- Value.asInt(x);
      var yi :- Value.asInt(y);
      Ok(Value.Bool(f(xi, yi)))
    }

    function applySetBinaryPred(f: (set<Value>, set<Value>) -> bool, x: Value, y: Value): Result<Value> {
      var xs :- Value.asSet(x);
      var ys :- Value.asSet(y);
      Ok(Value.Bool(f(xs, ys)))
    }

    predicate entityInEntity(x: EntityUID, y: EntityUID) {
      x == y ||
      (store.getEntityAttrs(x).Ok? &&
       store.entityIn(x, y))
    }

    // Returns true iff ys contains at least one element y such that
    // entityInEntity(x, y) holds.
    predicate entityInSetOfEntities(x: EntityUID, ys: set<EntityUID>)
    {
      exists y | y in ys :: entityInEntity(x, y)
    }

    function checkEntitySet(ys: set<Value>): Result<set<EntityUID>>
    {
      if forall y | y in ys :: Value.asEntity(y).Ok? then
        Ok(set y | y in ys :: y.primitive.uid)
      else
        Err(TypeError)
    }

    function applyBinaryOp(bop: BinaryOp, x: Value, y: Value): Result<Value> {
      match bop {
        case Eq =>     Ok(Value.Bool(x == y))
        case Less =>   applyIntBinaryPred((a, b) => a < b, x, y)
        case LessEq => applyIntBinaryPred((a, b) => a <= b, x, y)
        case Add =>    applyIntBinaryOp((a, b) => a + b, x, y)
        case Sub =>    applyIntBinaryOp((a, b) => a - b, x, y)
        case In =>
          var e :- Value.asEntity(x);
          if y.Set? then
            var uids :- checkEntitySet(y.s);
            Ok(Value.Bool(entityInSetOfEntities(e, uids)))
          else
            var g :- Value.asEntity(y);
            Ok(Value.Bool(entityInEntity(e, g)))
        case Contains =>
          var s :- Value.asSet(x);
          Ok(Value.Bool(y in s))
        case ContainsAll =>
          applySetBinaryPred((xs, ys) => xs >= ys, x, y)
        case ContainsAny =>
          applySetBinaryPred((xs, ys) => xs * ys != {}, x, y)
      }
    }
  }
}
