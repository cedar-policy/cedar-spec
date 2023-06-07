include "def.dfy"
include "../def/std.dfy"
include "../def/base.dfy"
include "../def/core.dfy"
include "../def/engine.dfy"
include "environment.dfy"

module pe.engine {
  import opened definition
  import opened def.std
  import opened def.base
  import opened def.core
  import opened def.engine
  import opened environment

  datatype PartialEvaluator = PartialEvaluator(request: definition.Request, store: definition.EntityStore) {

    function interpret(expr: definition.Expr): definition.Result<Residual> {
      match expr {
        case PrimitiveLit(p) => Ok(Concrete(Primitive(p)))
        case Var(v) =>
          match v {
            case Principal => Ok(Residual.fromRequestEntity(request.principal))
            case Action => Ok(Residual.fromRequestEntity(request.action))
            case Resource => Ok(Residual.fromRequestEntity(request.resource))
            case Context => Ok(Residual.fromRecord(request.context))
          }
        case If(e_cond, e_true, e_false) =>
          var v_cond :- interpret(e_cond);
          match v_cond {
            case Concrete(v) =>
              var b_cond :- Value.asBool(v);
              if b_cond then interpret(e_true) else interpret(e_false)
            case _ =>
              match (interpret(e_true), interpret(e_false)) {
                // ignore the error of the else branch
                case (Err(err1), Err(_)) => Err(err1)
                case (Ok(Concrete(v1)), Ok(Concrete(v2))) => Ok(Residual.If(v_cond, Concrete(v1), Concrete(v2)))
                case (Ok(Concrete(v1)), Ok(r2)) => Ok(Residual.If(v_cond, Concrete(v1), r2))
                case (Ok(r1), Ok(Concrete(v2))) => Ok(Residual.If(v_cond, r1, Concrete(v2)))
                case (Ok(r1), Ok(r2)) => Ok(Residual.If(v_cond, r1, r2))
                case (Err(_), Ok(r2)) => Ok(Residual.If(v_cond, makeErrorValue(), r2))
                case (Ok(r1), Err(_)) => Ok(Residual.If(v_cond, r1, makeErrorValue()))
              }
          }
        case BinaryApp(op, e1, e2) =>
          var r1 :- interpret(e1);
          var r2 :- interpret(e2);
          match (r1, r2) {
            case (Concrete(v1), Concrete(v2)) => Evaluator.applyBinaryOpGeneric(op, v1, v2, store).Map(v => Concrete(v))
            case (Concrete(v), _) => Ok(Residual.BinaryApp(op, Concrete(v), r2))
            case (_, Concrete(v)) => Ok(Residual.BinaryApp(op, r1, Concrete(v)))
            case _ => Ok(Residual.BinaryApp(op, r1, r2))
          }
        case UnaryApp(op, e) =>
          var r :- interpret(e);
          match r {
            case Concrete(v) =>
              var cv :- Evaluator.applyUnaryOp(op, v);
              Ok(Concrete(cv))
            case _ => Ok(Residual.UnaryApp(op, r))
          }
        case GetAttr(e, a) =>
          var r :- interpret(e);
          match r {
            case Concrete(v) =>
              if v.Record? then
                if a in v.record.Keys then Ok(Concrete(v.record[a])) else Err(AttrDoesNotExist)
              else
                var uid :- Value.asEntity(v);
                var res :- store.getEntityAttrs(uid);
                if a in res.Keys then Ok(res[a]) else Err(AttrDoesNotExist)
            case _ => Ok(Residual.GetAttr(r, a))
          }
        case HasAttr(e, a) =>
          var r :- interpret(e);
          match r {
            case Concrete(v) =>
              if v.Record? then
                Ok(Concrete(Value.Bool(a in v.record.Keys)))
              else
                var uid :- Value.asEntity(v);
                var res :- store.getEntityAttrs(uid);
                Ok(Concrete(Value.Bool(a in res.Keys)))
            case _ => Ok(Residual.GetAttr(r, a))
          }
        case Set(es) =>
          var rs :- interpretSeq(es);
          Ok(splitSeqToSet(rs))
        case Record(bs) =>
          var rs :- interpretRecord(bs);
          Ok(splitRecord(rs))
        case Unknown(u) => Ok(Residual.Unknown(u))
        case And(e1, e2) =>
          var l :- interpret(e1);
          match l {
            case Concrete(v1) =>
              var b :- Value.asBool(v1);
              if !b
              then Ok(l)
              else
                var r :- interpret(e2);
                match r {
                  case Concrete(v2) =>
                    Value.asBool(v2).Map(v => Concrete(v2))
                  case _ => Ok(Residual.And(l, r))
                }
            case _ =>
              var rr := interpret(e2);
              Ok(Residual.And(l, match rr {
                                case Ok(r) =>
                                  r
                                case _ => makeErrorValue()
                              }))
          }
        case Or(e1, e2) =>
          var l :- interpret(e1);
          match l {
            case Concrete(v1) =>
              var b :- Value.asBool(v1);
              if b
              then Ok(l)
              else
                var r :- interpret(e2);
                match r {
                  case Concrete(v2) =>
                    Value.asBool(v2).Map(v => Concrete(v2))
                  case _ => Ok(Residual.Or(l, r))
                }
            case _ =>
              var rr := interpret(e2);
              Ok(Residual.Or(l, match rr {
                               case Ok(r) =>
                                 r
                               case _ => makeErrorValue()
                             }))
          }
        case Call(fn, args) =>
          var rs :- interpretSeq(args);
          if (forall r | r in rs :: r.Concrete?) then
            Evaluator.applyExtFun(fn, seq(|rs|, i requires 0 <= i < |rs| => rs[i].v)).Map(v => Concrete(v))
          else
            Ok(Residual.Call(fn, rs))
      }
    }

    function makeErrorValue(): (r : Residual)
      ensures forall env : Environment :: env.wellFormed() ==> env.interpret(r).Err?
    {
      Residual.GetAttr(Residual.Record([]), "")
    }

    function interpretSeq(es: seq<definition.Expr>): definition.Result<seq<Residual>> {
      if |es| == 0 then
        Ok([])
      else
        var r :- interpret(es[0]);
        var rs :- interpretSeq(es[1..]);
        Ok([r] + rs)
    }

    function splitSeqToSet(rs: seq<Residual>): Residual {
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
