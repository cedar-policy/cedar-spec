include "def.dfy"
include "environment.dfy"
include "engine.dfy"
include "util.dfy"
include "eval.dfy"
include "../def/core.dfy"
include "../def/base.dfy"
include "../def/engine.dfy"
include "../def/std.dfy"

module pe.soundness {
  import opened definition
  import opened environment
  import opened engine
  import ce = def.engine
  import def.core
  import def.base
  import opened def.std
  import util
  import eval

  lemma PEIsSoundSet(e: definition.Expr, es: seq<definition.Expr>, q: core.Request, s: core.EntityStore, Q: definition.Request, S: definition.EntityStore, env: Environment)
    requires e == definition.Expr.Set(es)
    requires env.wellFormed() && restrictedEntityStore(S) && (var pr := env.replaceUnknownInRequest(Q); pr.Some? && pr.value == q) &&
             (var ps := env.replaceUnknownInEntityStore(S); ps.Some? && ps.value == s)
    ensures var peRes := PartialEvaluator(Q, S).interpret(e);
            (peRes.Ok? ==> util.relaxedEq(ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e)), env.interpret(peRes.value, s))) &&
            (peRes.Err? ==> ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e)).Err?) {
    var PE := PartialEvaluator(Q, S);
    var CE := ce.Evaluator(q, s);
    var peRes := PartialEvaluator(Q, S).interpret(e);
    forall e' | e' in es {
      PEIsSound(e', q, s, Q, S, env);
    }
    var rs := PE.interpretSeq(es);
    eval.PEInterpretSetMapReduce(es, PE);
    eval.CEInterpretSet(e, CE, env);

    var ceI := e' requires e' < e => CE.interpret(env.replaceUnknownInExpr(e'));
    var envI := e' requires PE.interpret(e').Ok? => env.interpret(PE.interpret(e').value, s);
    assert CE.interpret(env.replaceUnknownInExpr(e)) == util.CollectToSet(util.Map(es, ceI)).Map(v => core.Value.Set(v));
    if rs.Ok? {
      eval.PEInterpretSeqOk(es, PE);
      util.CollectToSeqOk(util.Map(es, PE.interpret));
      assert
        rs.value ==
        util.Map(util.Map(es, PE.interpret), (r: definition.Result<Residual>) requires r.Ok? => r.value) ==
        util.Map(es, e' requires PE.interpret(e').Ok? => PE.interpret(e').value);

      assert forall i: nat | i < |rs.value| :: rs.value[i] == PE.interpret(es[i]).value;

      if (forall r | r in rs.value :: r.Concrete?) {
        calc == {
          env.interpret(peRes.value, s);
          env.interpret(PE.splitSeqToSet(rs.value), s);
          env.interpret(Concrete(core.Value.Set(set x | x in rs.value :: x.v)), s);
          Ok(core.Value.Set(set x | x in rs.value :: x.v));
        }

        assert forall i: nat | i < |es| :: env.interpret(PE.interpret(es[i]).value, s).Ok?;
        assert forall e' | e' in es :: env.interpret(PE.interpret(e').value, s).Ok?;
        assert forall e' | e' in es :: env.interpret(PE.interpret(e').value, s) == CE.interpret(env.replaceUnknownInExpr(e'));
        util.MapEqvFunc(es, ceI, envI);
        assert forall e' | e' in es :: e' < e && PE.interpret(e').Ok?;
        calc == {
          util.Map(es, ceI);
          util.Map(es, envI);
        }
        calc == {
          util.Map(rs.value, r => env.interpret(r, s));
          util.Map(util.Map(es, e' requires PE.interpret(e').Ok? => PE.interpret(e').value), r => env.interpret(r, s));
          util.Map(es, envI);
        }
        assert util.Map(e.es, e' => CE.interpret(env.replaceUnknownInExpr(e'))) == util.Map(rs.value, r => env.interpret(r, s));
        calc == {
          util.Map(rs.value, r => env.interpret(r, s));
          util.Map(rs.value, (r: Residual) requires r.Concrete? => Ok(r.v));
        }
        util.CollectToSetWithMap(rs.value, (r: Residual) requires r.Concrete? => definition.Result<core.Value>.Ok(r.v));
        assert util.CollectToSet(util.Map(rs.value, (r: Residual) requires r.Concrete? => definition.Result<core.Value>.Ok(r.v))).value == set x | x in rs.value :: x.v;
        calc == {
          CE.interpret(env.replaceUnknownInExpr(e));
          util.CollectToSet(util.Map(e.es, envI)).Map(v => core.Value.Set(v));
          util.CollectToSet(util.Map(rs.value, r => env.interpret(r, s))).Map(v => core.Value.Set(v));
          util.CollectToSet(util.Map(rs.value, (r: Residual) requires r.Concrete? => Ok(r.v))).Map(v => core.Value.Set(v));
          Ok(core.Value.Set(set x | x in rs.value :: x.v));
        }
      } else {
        eval.PEInterpretSet(e, PE, env, s);

        var rs1 := util.Map(es, envI);
        var rs2 := util.Map(es, ceI);
        assert CE.interpret(env.replaceUnknownInExpr(e)) == util.CollectToSet(rs2).Map(v => core.Value.Set(v));
        assert (forall i: nat | i < |es| :: PE.interpret(es[i]).Ok?) && env.interpret(PE.interpret(e).value, s) == util.CollectToSet(rs1).Map(v => core.Value.Set(v));
        assert forall i : nat | i < |es| :: util.relaxedEq(ceI(es[i]), envI(es[i])) by {
          forall i : nat | i < |es| {
            PEIsSound(es[i], q, s, Q, S, env);
          }
        }
        //util.MapRel(es, ceI, envI, util.relaxedEq);
        assert CE.interpret(env.replaceUnknownInExpr(e)) ==
               util.CollectToSet(rs2).Map(v => core.Value.Set(v));
        assert util.relaxedEqSeq(rs1, rs2);
        util.CollectToSetRelaxedEq(rs1, rs2);
      }
    } else {
      eval.PEInterpretSeqErr(es, PE);
      assert exists e' | e' in es :: PE.interpret(e').Err?;
      assert exists e' | e' in es :: CE.interpret(env.replaceUnknownInExpr(e')).Err?;
      assert exists i: nat | i < |es| :: CE.interpret(env.replaceUnknownInExpr(es[i])).Err?;
      util.MapExists(es, ceI, (v: definition.Result<core.Value>) => v.Err?);
      assert exists r: definition.Result<core.Value>
          | r in util.Map(e.es, ceI) :: r.Err?;
      util.CollectToSetErr(util.Map(e.es, ceI));
      assert util.CollectToSet(util.Map(e.es, ceI)).Err?;
      assert CE.interpret(env.replaceUnknownInExpr(e)) ==
             util.CollectToSet(util.Map(es, ceI)).Map(v => core.Value.Set(v));
      assert CE.interpret(env.replaceUnknownInExpr(e)).Err?;
    }
  }

  lemma PEIsSoundAnd(e: definition.Expr, e1: definition.Expr, e2: definition.Expr, q: core.Request, s: core.EntityStore, Q: definition.Request, S: definition.EntityStore, env: Environment)
    requires e == definition.Expr.And(e1, e2)
    requires env.wellFormed() && restrictedEntityStore(S) && (var pr := env.replaceUnknownInRequest(Q); pr.Some? && pr.value == q) &&
             (var ps := env.replaceUnknownInEntityStore(S); ps.Some? && ps.value == s)
    ensures var peRes := PartialEvaluator(Q, S).interpret(e);
            (peRes.Ok? ==> util.relaxedEq(ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e)), env.interpret(peRes.value, s))) &&
            (peRes.Err? ==> ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e)).Err?)
  {
    var PE := PartialEvaluator(Q, S);
    var CE := ce.Evaluator(q, s);
    var peRes := PartialEvaluator(Q, S).interpret(e);
    var ceRes := CE.interpret(env.replaceUnknownInExpr(e));
    PEIsSound(e1, q, s, Q, S, env);
    PEIsSound(e2, q, s, Q, S, env);
    var reE1 := env.replaceUnknownInExpr(e1);
    var reE2 := env.replaceUnknownInExpr(e2);
    var ceRes1 := CE.interpret(reE1);
    var ceRes2 := CE.interpret(reE2);
    var errV := PE.makeErrorValue();
    calc == {
      ceRes;
      CE.interpret(core.And(reE1, reE2));
    }
    match PE.interpret(e1) {
      case Ok(r1) => match r1 {
        case Concrete(v1) => assume false;
        case _ =>
          match PE.interpret(e2) {
            case Ok(r2) => assume false;
            case Err(_) =>
              calc == {
                peRes;
                Ok(Residual.And(r1, errV));
              }
              calc == {
                env.interpret(peRes.value, s);
                env.interpret(Residual.And(r1, errV), s);
              }
              if env.interpret(r1, s).Err? {
                eval.InterpretResidualAndErr(env, r1, errV, s);
                assert env.interpret(Residual.And(r1, errV), s).Err?;
                assert CE.interpret(reE1).Err? by {
                  assert util.relaxedEq(env.interpret(r1, s), ceRes1);
                }
                assert CE.interpret(core.And(env.replaceUnknownInExpr(e1), env.replaceUnknownInExpr(e2))).Err?;
              } else {
                if core.Value.asBool(env.interpret(r1, s).value).Err? {
                  assert env.interpret(Residual.And(r1, errV), s).Err?;
                  assert core.Value.asBool(ceRes1.value).Err?;
                  assert  CE.interpret(core.And(reE1, reE2)).Err?;
                } else {
                  var b := core.Value.asBool(env.interpret(r1, s).value).value;
                  assert CE.interpret(env.replaceUnknownInExpr(e1)).Ok?;
                  assert CE.interpret(env.replaceUnknownInExpr(e1)).value == core.Value.Bool(b);
                  if b {
                    eval.MakeErrorValueIsErr(env, s);
                    assert CE.interpret(env.replaceUnknownInExpr(e2)).Err?;
                    assert CE.interpret(core.And(env.replaceUnknownInExpr(e1), env.replaceUnknownInExpr(e2))) == CE.interpret(env.replaceUnknownInExpr(e2));
                    assert CE.interpret(env.replaceUnknownInExpr(e)).Err?;
                    assert env.interpret(Residual.And(r1, PE.makeErrorValue()), s) == env.interpret(PE.makeErrorValue(), s);
                    assert env.interpret(PE.makeErrorValue(), s).Err?;
                  } else {
                    assert CE.interpret(core.And(env.replaceUnknownInExpr(e1), env.replaceUnknownInExpr(e2))) == Ok(core.Value.Bool(false));
                    assert  env.interpret(Residual.And(r1, PE.makeErrorValue()), s) == Ok(core.Value.Bool(false));
                  }
                }
              }

          }
      }
      case Err(_) =>
    }
  }

  lemma PEIsSound(e: definition.Expr, q: core.Request, s: core.EntityStore, Q: definition.Request, S: definition.EntityStore, env: Environment)
    decreases e
    requires env.wellFormed() && restrictedEntityStore(S) && (var pr := env.replaceUnknownInRequest(Q); pr.Some? && pr.value == q) &&
             (var ps := env.replaceUnknownInEntityStore(S); ps.Some? && ps.value == s)
    ensures var peRes := PartialEvaluator(Q, S).interpret(e);
            // If PE succeeds, then evaluating the residual and evaluating the original expression with the same unknown to value mappings should agree.
            (peRes.Ok? ==> util.relaxedEq(ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e)), env.interpret(peRes.value, s))) &&
            // If PE fails, then evaluating the original expression with any uknown to value mappings should fail.
            (peRes.Err? ==> ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e)).Err?)
  {
    var peRes := PartialEvaluator(Q, S).interpret(e);
    var PE := PartialEvaluator(Q, S);
    var CE := ce.Evaluator(q, s);
    match e {
      case PrimitiveLit(_) =>
      case Var(Principal) =>
      case Var(Action) =>
      case Var(Resource) =>
      case Var(Context) =>
        var peContext := peRes.value;
        // peContext is a seq of pairs (Attr, Residual) or concrete Value.Record
        assert peContext == Residual.fromRecord(Q.context);
        // environment interpreter interprets (Attr, Residual) into map<Attr, Value>
        // replaceUknownInContext converts map<Attr, Residual> into Option<map<Attr, Value>>
        // left result
        assert ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e)) == Ok(core.Value.Record(q.context));
        if peContext.Concrete? {
          assert env.interpret(peContext, s).value.record == env.replaceRecord(Q.context).value;
        } else {
          assume false;
        }
      case UnaryApp(op, arg) =>
        assert {:split_here} true;
        PEIsSound(arg, q, s, Q, S, env);
      case BinaryApp(op, arg1, arg2) =>
        assert {:split_here} true;
        PEIsSound(arg1, q, s, Q, S, env);
        PEIsSound(arg2, q, s, Q, S, env);
      case GetAttr(se, a) =>
        assert {:split_here} true;
        var peRes' := PartialEvaluator(Q, S).interpret(se);
        PEIsSound(se, q, s, Q, S, env);
        if peRes'.Ok? {
          var peVal' := peRes'.value;
          if peVal'.Concrete? {
            var concreteVal' := peVal'.v;
            match concreteVal' {
              case Primitive(EntityUID(euid)) =>
                if euid in s.entities.Keys {
                  if a in s.entities[euid].attrs.Keys {
                    assert restrictedEntityData(S.entities[euid]);
                    eval.InterpretRestrictedResidual(S.entities[euid].attrs[a], env, s);
                  }
                }
              case _ =>
            }
          }
        }
      case HasAttr(se, a) =>
        assert {:split_here} true;
        PEIsSound(se, q, s, Q, S, env);
      case Set(es) =>
        assert {:split_here} true;
        PEIsSoundSet(e, es, q, s, Q, S, env);
      case And(e1, e2) =>
        assert {:split_here} true;
        PEIsSoundAnd(e, e1, e2, q, s, Q, S, env);
      case _ => assume false;
    }
  }
}
