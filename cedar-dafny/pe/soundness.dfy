include "def.dfy"
include "interpretation.dfy"
include "engine.dfy"
include "../def/core.dfy"
include "../def/engine.dfy"

module pe.soundness {
  import opened definition
  import opened interpretation
  import opened engine
  import ce = def.engine
  import def.core

  lemma PEIsSound(e: definition.Expr, q: core.Request, s: core.EntityStore, Q: definition.Request, S: definition.EntityStore, I: Interpretation)
    requires I.wellFormed()
    requires var pr := I.replaceUnknownInRequest(Q); pr.Some? && pr.value == q
    requires var ps := I.replaceUnknownInEntityStore(S); ps.Some? && ps.value == s
    ensures var peRes := PartialEvaluator(Q, S).interpret(e);
            (peRes.Ok? ==> ce.Evaluator(q, s).interpret(I.replaceUnknownInExpr(e)) == I.interpret(peRes.value)) &&
            (peRes.Err? ==> ce.Evaluator(q, s).interpret(I.replaceUnknownInExpr(e)).Err?)
}
