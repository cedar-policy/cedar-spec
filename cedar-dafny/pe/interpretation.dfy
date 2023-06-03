include "../def/core.dfy"
include "../def/base.dfy"
include "../difftest/main.dfy"
include "../def/std.dfy"
include "def.dfy"

module pe.interpretation {
  import opened def.core
  import opened def.base
  import difftest.restrictedExpr
  import opened def.std
  import opened definition

  // The interpretation class
  datatype Interpretation = Interpretation(mappings: string -> core.Expr) {
    ghost predicate wellFormed() {
      forall v :: restrictedExpr.evaluate(mappings(v)).Some?
    }

    function interpret(r: Residual): definition.Result<core.Value>
      requires wellFormed()
    {
      match r {
        case Concrete(v) => Ok(v)
        case If(c, t, e) => Err(TypeError)
        case Unknown(u: Unknown) => Ok(restrictedExpr.evaluate(mappings(u.name)).value)
        case _ => Err(TypeError)
      }
    }

    function replaceUnknownInOptionalEntity(oe: OptionalEntity): (r: Option<core.EntityUID>)
      requires wellFormed()
    {
      match oe {
        case Left(l) => Some(l)
        case Right(u) =>
          var v := restrictedExpr.evaluate(mappings(u.name)).value;
          if v.Primitive? && v.primitive.EntityUID? then
            Some(v.primitive.uid)
          else
            None
      }
    }

    function replaceRecord(context: definition.Record): Option<core.Record>
      requires wellFormed() {
      var nr := map a: Attr | a in context.Keys :: interpret(context[a]);
      if forall a | a in nr.Keys :: nr[a].Ok? then
        Some(map a | a in nr.Keys :: nr[a].value)
      else
        None
    }

    function replaceUnknownInRequest(req: definition.Request): Option<core.Request>
      requires wellFormed()
    {
      var p :- replaceUnknownInOptionalEntity(req.principal);
      var a :- replaceUnknownInOptionalEntity(req.action);
      var r :- replaceUnknownInOptionalEntity(req.resource);
      var c :- replaceRecord(req.context);
      Some(core.Request(p, a, r, c))
    }

    function replaceUnknownInEntityStore(store: definition.EntityStore): Option<core.EntityStore>
      requires wellFormed() {
      var entities := map euid: EntityUID | euid in store.entities.Keys :: match replaceRecord(store.entities[euid].attrs) {
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
