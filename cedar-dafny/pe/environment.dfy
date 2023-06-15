include "../def/core.dfy"
include "../def/base.dfy"
include "../difftest/main.dfy"
include "../def/std.dfy"
include "../def/engine.dfy"
include "def.dfy"

module pe.environment {
  import opened def.core
  import opened def.base
  import difftest.restrictedExpr
  import opened def.std
  import opened definition
  import opened def.engine

  // Like the interpretation in the symbolic evaluator, this datatype contains a mapping from unknowns to values.
  // But we can't use `Value` as the codomain because replacing uknowns in an policy body requires them to be `Expr`s.
  // We add a wellFormed predicate to constrain that the codomain `Expr`s ought to be evaluated into `Value`s.
  datatype Environment = Environment(mappings: string -> core.Expr) {
    ghost predicate wellFormed() {
      forall v :: restrictedExpr.evaluate(mappings(v)).Some?
    }

    function interpret(residual: Residual, entities: core.EntityStore): definition.Result<core.Value>
      requires wellFormed()
    {
      match residual {
        case Concrete(v) => Ok(v)
        case If(c, t, e) =>
          var cv :- interpret(c, entities);
          var cb :- Value.asBool(cv);
          if cb then interpret(t, entities) else interpret(e, entities)
        case And(r1, r2) =>
          var v1 :- interpret(r1, entities);
          var b1 :- Value.asBool(v1);
          if b1 then interpret(r2, entities) else Ok(Value.Bool(false))
        case Or(r1, r2) =>
          var v1 :- interpret(r1, entities);
          var b1 :- Value.asBool(v1);
          if b1 then Ok(Value.Bool(true)) else interpret(r2, entities)
        case UnaryApp(op, r) =>
          var v :- interpret(r, entities);
          Evaluator.applyUnaryOp(op, v)
        case BinaryApp(op, r1, r2) =>
          var v1 :- interpret(r1, entities);
          var v2 :- interpret(r2, entities);
          Evaluator.applyBinaryOpGeneric(op, v1, v2, entities)
        case GetAttr(r, a) =>
          var v :- interpret(r, entities);
          var rec :- Evaluator.expectRecordDerefEntityWithStore(v, false, entities);
          if a in rec.Keys then Ok(rec[a]) else Err(AttrDoesNotExist)
        case HasAttr(r, a) =>
          var v :- interpret(r, entities);
          var rec :- Evaluator.expectRecordDerefEntityWithStore(v, true, entities);
          Ok(Value.Bool(a in rec.Keys))
        case Set(rs) =>
          var vs :- interpretSet(rs, entities);
          Ok(Value.Set(vs))
        case Record(bs) =>
          var fvs :- interpretRecord(bs, entities);
          Ok(Value.Record(fvs))
        case Call(name, rs) =>
          var args :- interpretList(rs, entities);
          Evaluator.applyExtFun(name, args)
        case Unknown(u: Unknown) => Ok(restrictedExpr.evaluate(mappings(u.name)).value)
      }
    }

    function interpretSet(rs: seq<Residual>, entities: core.EntityStore): definition.Result<set<Value>>
      requires wellFormed()
    {
      if rs == [] then
        Ok({})
      else
        var head_v :- interpret(rs[0], entities);
        var tail_vs :- interpretSet(rs[1..], entities);
        Ok({head_v} + tail_vs)
    }

    function interpretRecord(bs: seq<(Attr,Residual)>, entities: core.EntityStore): definition.Result<map<Attr, Value>>
      requires wellFormed()
    {
      if bs == [] then
        Ok(map[])
      else
        var k := bs[0].0;
        var v :- interpret(bs[0].1, entities);
        var m :- interpretRecord(bs[1..], entities);
        if k in m.Keys then // If the same field is repeated later in the record,
          Ok(m)             // we give that occurrence priority and ignore this one.
        else
          Ok(m[k := v])
    }

    function interpretList(rs: seq<Residual>, entities: core.EntityStore): definition.Result<seq<Value>>
      requires wellFormed()
    {
      if rs == [] then
        Ok([])
      else
        var head_v :- interpret(rs[0], entities);
        var tail_vs :- interpretList(rs[1..], entities);
        Ok([head_v] + tail_vs)
    }

    function replaceUnknownInRequestEntity(oe: RequestEntity): (r: Option<core.EntityUID>)
      requires wellFormed()
    {
      match oe {
        case Entity(e) => Some(e)
        case Uknown(u) =>
          var v := restrictedExpr.evaluate(mappings(u.name)).value;
          if v.Primitive? && v.primitive.EntityUID? then
            Some(v.primitive.uid)
          else
            None
      }
    }

    function replaceRecord(context: definition.Record): Option<core.Record>
      requires wellFormed() {
      var nr := map a: Attr | a in context.Keys :: interpret(context[a], core.EntityStore(map[]));
      if forall a | a in nr.Keys :: nr[a].Ok? then
        Some(map a | a in nr.Keys :: nr[a].value)
      else
        None
    }

    function replaceUnknownInRequest(req: definition.Request): Option<core.Request>
      requires wellFormed()
    {
      var p :- replaceUnknownInRequestEntity(req.principal);
      var a :- replaceUnknownInRequestEntity(req.action);
      var r :- replaceUnknownInRequestEntity(req.resource);
      var c :- replaceRecord(req.context);
      Some(core.Request(p, a, r, c))
    }

    function replaceUnknownInEntityStore(store: definition.EntityStore): Option<core.EntityStore>
      requires wellFormed() {
      var entities :=
        map euid: EntityUID
          | euid in store.entities.Keys ::
          match replaceRecord(store.entities[euid].attrs) {
            case Some(r) => Some(core.EntityData(r, store.entities[euid].ancestors))
            case None => None
          };
      if forall euid | euid in entities.Keys :: entities[euid].Some? then
        Some(core.EntityStore(map euid | euid in entities.Keys :: entities[euid].value))
      else
        None
    }

    function replaceUnknownInExpr(e: definition.Expr): core.Expr {
      match e {
        case PrimitiveLit(p) => core.PrimitiveLit(p)
        case Var(v) => core.Var(v)
        case If(c, t, else_e) => core.If(replaceUnknownInExpr(c), replaceUnknownInExpr(t), replaceUnknownInExpr(else_e))
        case And(e1, e2) => core.And(replaceUnknownInExpr(e1), replaceUnknownInExpr(e2))
        case Or(e1, e2) => core.Or(replaceUnknownInExpr(e1), replaceUnknownInExpr(e2))
        case UnaryApp(o, op_e) => core.UnaryApp(o, replaceUnknownInExpr(op_e))
        case BinaryApp(o, e1, e2) => core.BinaryApp(o, replaceUnknownInExpr(e1), replaceUnknownInExpr(e2))
        case GetAttr(entity_e, a) => core.GetAttr(replaceUnknownInExpr(entity_e), a)
        case HasAttr(entity_e, a) => core.HasAttr(replaceUnknownInExpr(entity_e), a)
        case Set(es) => core.Expr.Set(seq(|es|, i requires 0 <= i < |es| => replaceUnknownInExpr(es[i])))
        case Record(bs) => core.Expr.Record(seq(|bs|, i requires 0 <= i < |bs| => (bs[i].0, replaceUnknownInExpr(bs[i].1))))
        case Call(name, args) => core.Call(name, seq(|args|, i requires 0 <= i < |args| => replaceUnknownInExpr(args[i])))
        case Unknown(u) => mappings(u.name)
      }
    }
  }
}
