include "def.dfy"
include "environment.dfy"
include "engine.dfy"
include "../def/core.dfy"
include "../def/engine.dfy"

module pe.soundness {
  import opened definition
  import opened environment
  import opened engine
  import ce = def.engine
  import def.core

  lemma PEIsSound(e: definition.Expr, q: core.Request, s: core.EntityStore, Q: definition.Request, S: definition.EntityStore, env: Environment)
    requires env.wellFormed()
    requires var pr := env.replaceUnknownInRequest(Q); pr.Some? && pr.value == q
    requires var ps := env.replaceUnknownInEntityStore(S); ps.Some? && ps.value == s
    ensures var peRes := PartialEvaluator(Q, S).interpret(e);
            // If PE succeeds, then evaluating the residual and evaluating the original expression with the same unknown to value mappings should agree.
            (peRes.Ok? ==> ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e)) == env.interpret(peRes.value)) &&
            // If PE fails, then evaluating the original expression with any uknown to value mappings should fail.
            (peRes.Err? ==> ce.Evaluator(q, s).interpret(env.replaceUnknownInExpr(e)).Err?)
}
