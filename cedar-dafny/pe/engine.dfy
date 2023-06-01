include "def.dfy"
include "../def/std.dfy"
include "../def/base.dfy"
include "../def/core.dfy"
include "../def/engine.dfy"

module pe.engine {
  import opened definition
  import opened def.std
  import opened def.base
  import opened def.core
  import opened def.engine

  datatype Evaluator = Evaluator(request: definition.Request, store: definition.EntityStore) {

    function interpret(expr: definition.Expr): definition.Result<Residual> {
      match expr {
        case PrimitiveLit(p) => Ok(Concrete(Primitive(p)))
        case Var(v) =>
          match v {
            case Principal => Ok(Residual.fromOptionalEntity(request.principal))
            case Action => Ok(Residual.fromOptionalEntity(request.action))
            case Resource => Ok(Residual.fromOptionalEntity(request.resource))
            case Context => Ok(Residual.fromRecord(request.context))
          }
        case If(e_cond, e_true, e_false) =>
          var v_cond :- interpret(e_cond);
          match v_cond {
            case Concrete(v) =>
              var b_cond :- Value.asBool(v);
              if b_cond then interpret(e_true) else interpret(e_false)
            case _ => Err(TypeError)
          }
        case BinaryApp(op, e1, e2) =>
          var r1 :- interpret(e1);
          var r2 :- interpret(e2);
          match (r1, r2) {
            case (Concrete(v1), Concrete(v2)) => Err(TypeError)
            case _ => Err(TypeError)
          }
        case UnaryApp(op, e) =>
          var r :- interpret(e);
          match r {
            case Concrete(v) =>
              var cv :- engine.Evaluator.applyUnaryOp(op, v);
              Ok(Concrete(cv))
            case _ => Ok(Residual.UnaryApp(op, r))
          }
        case Set(es) =>
          var rs :- interpretSet(es);
          Ok(splitSeq(rs))
        case Record(bs) =>
          var rs :- interpretRecord(bs);
          Ok(splitRecord(rs))
        case Unknown(u) => Ok(Residual.Unknown(u))
        case _ => Err(TypeError)
      }
    }

    function interpretSet(es: seq<definition.Expr>): definition.Result<seq<Residual>> {
      if |es| == 0 then
        Ok([])
      else
        var r :- interpret(es[0]);
        var rs :- interpretSet(es[1..]);
        Ok([r] + rs)
    }

    function splitSeq(rs: seq<Residual>): Residual {
      if (forall r | r in rs :: r.Concrete?) then
        Concrete(Value.Set(set x | x in rs :: x.v))
      else
        Residual.Set(rs)
    }

    function interpretRecord(bs: seq<(Attr, definition.Expr)>): definition.Result<seq<(Attr, Residual)>> {
      if |bs| == 0 then
        Ok([])
      else
        var r :- interpret(bs[0].1);
        var rs :- interpretRecord(bs[1..]);
        Ok([(bs[0].0, r)] + rs)
    }

    function seqToMap(bs: seq<(Attr, Value)>): map<Attr, Value> {
      if |bs| == 0 then
        map[]
      else
        var m := seqToMap(bs[1..]);
        if bs[0].0 in m.Keys then
          m
        else
          m[bs[0].0 := bs[0].1]
    }

    function splitRecord(rs: seq<(Attr, Residual)>): Residual {
      if (forall b | b in rs :: b.1.Concrete?) then
        Concrete(Value.Record(seqToMap(seq(|rs|, i requires 0 <= i < |rs| => (rs[i].0, rs[i].1.v)))))
      else
        Residual.Record(rs)
    }
  }
}
