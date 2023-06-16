include "def.dfy"
include "environment.dfy"
include "engine.dfy"
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

  lemma MakeErrorValueIsErr(env: Environment)
    requires env.wellFormed()
    ensures var r := PartialEvaluator.makeErrorValue(); env.interpret(r, core.EntityStore(map[])).Err? {
    calc {
      env.interpret(PartialEvaluator.makeErrorValue(), core.EntityStore(map[]));
    ==
      calc {
        env.interpret(Residual.Record([]), core.EntityStore(map[]));
      ==
        Ok(core.Value.Record(map[]));
      }
      Err(base.AttrDoesNotExist);
    }
  }

  lemma InterpretRestrictedResidualSet(rs: seq<Residual>, env: Environment, s: core.EntityStore)
    requires forall r | r in rs :: r.restricted?()
    requires env.wellFormed()
    ensures env.interpretSet(rs, s) == env.interpretSet(rs, core.EntityStore(map[]))
  {
    if |rs| == 0 {

    } else {
      InterpretRestrictedResidual(rs[0], env, s);
    }
  }

  lemma InterpretRestrictedResidualRecord(bs: seq<(core.Attr, Residual)>, env: Environment, s: core.EntityStore)
    requires forall b | b in bs :: b.1.restricted?()
    requires env.wellFormed()
    ensures env.interpretRecord(bs, s) == env.interpretRecord(bs, core.EntityStore(map[]))
  {
    if |bs| == 0 {

    } else {
      InterpretRestrictedResidual(bs[0].1, env, s);
    }
  }

  lemma InterpretRestrictedResidualList(rs: seq<Residual>, env: Environment, s: core.EntityStore)
    requires forall r | r in rs :: r.restricted?()
    requires env.wellFormed()
    ensures env.interpretList(rs, s) == env.interpretList(rs, core.EntityStore(map[])) {
    if |rs| == 0 {

    } else {
      InterpretRestrictedResidual(rs[0], env, s);
    }
  }

  lemma InterpretRestrictedResidual(r: Residual, env: Environment, s: core.EntityStore)
    requires r.restricted?()
    requires env.wellFormed()
    ensures env.interpret(r, s) == env.interpret(r, core.EntityStore(map[]))
  {
    match r {
      case Concrete(_) =>
      case Unknown(_) =>
      case Set(rs) => InterpretRestrictedResidualSet(rs, env, s);
      case Record(bs) => InterpretRestrictedResidualRecord(bs, env, s);
      case Call(_, args) => InterpretRestrictedResidualList(args, env, s);
      case _ => assume false;
    }
  }

  lemma PEInterpretSeqOk(es: seq<definition.Expr>, pe: PartialEvaluator)
    requires pe.interpretSeq(es).Ok?
    ensures forall e | e in es :: pe.interpret(e).Ok?
  {

  }

  lemma PEInterpretSeqErr(es: seq<definition.Expr>, pe: PartialEvaluator)
    requires pe.interpretSeq(es).Err?
    ensures exists e | e in es :: pe.interpret(e).Err?
  {

  }

  lemma CEInterpretSetErr(es: seq<core.Expr>, ce: ce.Evaluator)
    requires exists e | e in es :: ce.interpret(e).Err?
    ensures ce.interpretSet(es).Err? {

  }

  // assert exists e | e in es :: I(R(e));
  // assert exists e' | e' in Map(R, es) :: I(e');
  lemma MappingPreservesPredicate<A, B>(es: seq<A>, R: A -> B, pred: B -> bool)
    requires exists e | e in es :: pred(R(e))
    ensures exists e' | e' in seq(|es|, i requires 0 <= i < |es| => R(es[i])) :: pred(e') {
    assert exists i | 0 <= i < |es| :: pred(R(es[i]));
    //assert forall e | e in es :: R(e) in seq(|es|, i requires 0 <= i < |es| => R(es[i]));
    assume false;
  }

  lemma PEIsSoundSet(e: definition.Expr, q: core.Request, s: core.EntityStore, Q: definition.Request, S: definition.EntityStore, env: Environment)
    requires env.wellFormed()
    requires restrictedEntityStore(S)
    requires e.Set?
    // Request is well formed
    requires var pr := env.replaceUnknownInRequest(Q); pr.Some? && pr.value == q
    // Entity store is well formed
    requires var ps := env.replaceUnknownInEntityStore(S); ps.Some? && ps.value == s
    ensures var peRes := PartialEvaluator(Q, S).interpret(e);
            // If PE succeeds, then evaluating the residual and evaluating the original expression with the same unknown to value mappings should agree.
            (peRes.Ok? ==> ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e)) == env.interpret(peRes.value, s)) &&
            // If PE fails, then evaluating the original expression with any uknown to value mappings should fail.
            (peRes.Err? ==> ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e)).Err?)
  {
    var PE := PartialEvaluator(Q, S);
    var CE := ce.Evaluator(q, s);
    var peRes := PE.interpret(e);
    match e {
      case Set(es) =>
        forall e' | e' in es {
          PEIsSound(e', q, s, Q, S, env);
        }
        var rs := PE.interpretSeq(es);
        if rs.Ok? {
          PEInterpretSeqOk(es, PE);
          assert forall e' | e' in es :: PE.interpret(e').Ok?;
          /*
          assume forall i | 0 <= i < |es| :: ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(es[i])) == env.interpret(rs.value[i], s);
          assume rs.value == seq(|es|, i requires 0 <= i < |es| => PartialEvaluator(Q, S).interpret(es[i]).value);
          if (forall r | r in rs.value :: r.Concrete?) {
            calc == {
              ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e));
              ce.Evaluator(q, s).interpret(core.Expr.Set(seq(|es|, i requires 0 <= i < |es| => env.replaceUnknownInExpr(es[i]))));
              ce.Evaluator(q, s).interpretSet(seq(|es|, i requires 0 <= i < |es| => env.replaceUnknownInExpr(es[i]))).Map(v => core.Value.Set(v));
              env.interpret(PartialEvaluator(Q, S).splitSeqToSet(rs.value), s);
            }
          } else {
            calc == {
              env.interpret(PartialEvaluator(Q, S).splitSeqToSet(rs.value), s);
              env.interpret(Residual.Set(rs.value), s);
              env.interpretSet(rs.value, s).Map(v => core.Value.Set(v));
              env.interpretSet(seq(|es|, i requires 0 <= i < |es| => PartialEvaluator(Q, S).interpret(es[i]).value), s).Map(v => core.Value.Set(v));
            }
          }
          */
          assume false;
        } else {
          PEInterpretSeqErr(es, PE);
          assert exists e' | e' in es :: PE.interpret(e').Err?;
          assert exists e' | e' in es :: CE.interpret(env.replaceUnknownInExpr(e')).Err?;
          assume exists e' | e' in seq(|es|, i requires 0 <= i < |es| => env.replaceUnknownInExpr(es[i])) :: CE.interpret(e').Err?;
          CEInterpretSetErr(seq(|es|, i requires 0 <= i < |es| => env.replaceUnknownInExpr(es[i])), CE);
          calc == {
            CE.interpret(env.replaceUnknownInExpr(e));
            CE.interpret(core.Expr.Set(seq(|es|, i requires 0 <= i < |es| => env.replaceUnknownInExpr(es[i]))));
            CE.interpretSet(seq(|es|, i requires 0 <= i < |es| => env.replaceUnknownInExpr(es[i]))).Map(v => core.Value.Set(v));
          }
        }
    }
  }

  lemma PEIsSound(e: definition.Expr, q: core.Request, s: core.EntityStore, Q: definition.Request, S: definition.EntityStore, env: Environment)
    requires env.wellFormed()
    requires restrictedEntityStore(S)
    // Request is well formed
    requires var pr := env.replaceUnknownInRequest(Q); pr.Some? && pr.value == q
    // Entity store is well formed
    requires var ps := env.replaceUnknownInEntityStore(S); ps.Some? && ps.value == s
    ensures var peRes := PartialEvaluator(Q, S).interpret(e);
            // If PE succeeds, then evaluating the residual and evaluating the original expression with the same unknown to value mappings should agree.
            (peRes.Ok? ==> ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e)) == env.interpret(peRes.value, s)) &&
            // If PE fails, then evaluating the original expression with any uknown to value mappings should fail.
            (peRes.Err? ==> ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e)).Err?)
  {
    var peRes := PartialEvaluator(Q, S).interpret(e);
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
        PEIsSound(arg, q, s, Q, S, env);
      case BinaryApp(op, arg1, arg2) =>
        PEIsSound(arg1, q, s, Q, S, env);
        PEIsSound(arg2, q, s, Q, S, env);
      case GetAttr(se, a) =>
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
                    InterpretRestrictedResidual(S.entities[euid].attrs[a], env, s);
                  }
                }
              case _ =>
            }
          }
        }
      case HasAttr(se, a) =>
        PEIsSound(se, q, s, Q, S, env);
      case Set(es) => assume false;
      case _ => assume false;
    }
  }
}
