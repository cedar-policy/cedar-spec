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

  lemma makeErrorValueIsErr(env: Environment)
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

  lemma PEIsSoundGetAttr(e: definition.Expr, q: core.Request, s: core.EntityStore, Q: definition.Request, S: definition.EntityStore, env: Environment)
    requires env.wellFormed()
    requires e.GetAttr?
    // Request is well formed
    requires var pr := env.replaceUnknownInRequest(Q); pr.Some? && pr.value == q
    // Entity store is well formed
    requires var ps := env.replaceUnknownInEntityStore(S); ps.Some? && ps.value == s
    ensures var peRes := PartialEvaluator(Q, S).interpret(e);
            // If PE succeeds, then evaluating the residual and evaluating the original expression with the same unknown to value mappings should agree.
            (peRes.Ok? ==> ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e)) == env.interpret(peRes.value, s)) &&
            // If PE fails, then evaluating the original expression with any uknown to value mappings should fail.
            (peRes.Err? ==> ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e)).Err?) {
    var peRes := PartialEvaluator(Q, S).interpret(e);
    match e {

      case GetAttr(se, a) =>
        var peRes' := PartialEvaluator(Q, S).interpret(se);
        PEIsSound(se, q, s, Q, S, env);
        if peRes'.Err? {

        } else {
          var peVal' := peRes'.value;
          if peVal'.Concrete? {
            var concreteVal' := peVal'.v;
            match concreteVal' {
              case Primitive(EntityUID(euid)) =>
                if euid in s.entities.Keys {
                  if a in s.entities[euid].attrs.Keys {
                    calc == {
                      ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e));
                      Ok(s.entities[euid].attrs[a]);
                    }
                    calc == {
                      peRes;
                      Ok(S.entities[euid].attrs[a]);
                    }
                    assume env.interpret(S.entities[euid].attrs[a], s).Ok? && env.interpret(S.entities[euid].attrs[a], s).value == s.entities[euid].attrs[a];
                    //calc == {
                    //  env.interpret(peRes.value, s);
                    //  Ok(s.entities[euid].attrs[a]);
                    //}
                  } else {

                  }


                } else {
                }
              case _ =>

            }
          } else {

          }
        }
    }
  }

  lemma PEIsSound(e: definition.Expr, q: core.Request, s: core.EntityStore, Q: definition.Request, S: definition.EntityStore, env: Environment)
    requires env.wellFormed()
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
      case _ => assume false;
    }
  }
}
