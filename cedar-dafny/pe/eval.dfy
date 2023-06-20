include "def.dfy"
include "util.dfy"
include "environment.dfy"
include "../def/core.dfy"
include "../def/base.dfy"
include "../def/engine.dfy"
include "../def/std.dfy"

module pe.eval {
  import opened definition
  import ce = def.engine
  import def.core
  import def.base
  import opened def.std
  import util
  import environment

  lemma CEInterpretSetMapReduce(es: seq<core.Expr>, ce: ce.Evaluator)
    ensures ce.interpretSet(es) == util.CollectToSet(util.Map(es, ce.interpret))
  {
    if |es| > 0 {
      assert util.Map(es, ce.interpret) == [ce.interpret(es[0])] + util.Map(es[1..], ce.interpret);
    }
  }

  lemma MapCompose<T, X, Y>(es: seq<T>, f: (T --> X), g: (X -> Y))
    requires forall i :: 0 <= i < |es| ==> f.requires(es[i])
    ensures util.Map(util.Map(es, f), g) == util.Map(es, e requires f.requires(e) => g(f(e))) {
    if |es| == 0 {
      assume false;
    } else {
      MapCompose(es[1..], f, g);
      assert util.Map(util.Map(es, f), g) == util.Map([f(es[0])] + util.Map(es[1..], f), g) == [g(f(es[0]))] + util.Map(util.Map(es[1..], f), g);
      assert util.Map(es, e requires f.requires(e) => g(f(e))) == [g(f(es[0]))] + util.Map(es[1..], e requires f.requires(e) => g(f(e)));
    }
  }

  lemma CEInterpretSet(e: definition.Expr, CE: ce.Evaluator, env: environment.Environment)
    requires e.Set?
    requires env.wellFormed()
    ensures CE.interpret(env.replaceUnknownInExpr(e)) == util.CollectToSet(util.Map(e.es, e' requires e' < e => CE.interpret(env.replaceUnknownInExpr(e')))).Map(v => core.Value.Set(v)) {
    CEInterpretSetMapReduce(util.Map(e.es, e' requires e' < e => env.replaceUnknownInExpr(e')), CE);
    MapCompose(e.es, e' requires e' < e => env.replaceUnknownInExpr(e'), CE.interpret);
    assert util.Map(util.Map(e.es, e' requires e' < e => env.replaceUnknownInExpr(e')), CE.interpret) == util.Map(e.es, e' requires e' < e => CE.interpret(env.replaceUnknownInExpr(e')));
    calc == {
      CE.interpret(env.replaceUnknownInExpr(e));
      CE.interpret(core.Expr.Set(util.Map(e.es, e' requires e' < e => env.replaceUnknownInExpr(e'))));
      CE.interpretSet(util.Map(e.es, e' requires e' < e => env.replaceUnknownInExpr(e'))).Map(v => core.Value.Set(v));
      util.CollectToSet(util.Map(util.Map(e.es, e' requires e' < e => env.replaceUnknownInExpr(e')), CE.interpret)).Map(v => core.Value.Set(v));
      util.CollectToSet(util.Map(e.es, e' requires e' < e => CE.interpret(env.replaceUnknownInExpr(e')))).Map(v => core.Value.Set(v));
    }

  }
}
