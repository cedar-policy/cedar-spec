include "../def/all.dfy"

module validation.util {
  import opened def.base
  import opened def.core
  import opened def.engine

  // --------- Replace a variable with a literal entity UID --------- //

  function substitute(e: Expr, v: Var, euid: EntityUID): Expr {
    match e {
      case PrimitiveLit(_) => e
      case Var(v') =>
        if v == v' then PrimitiveLit(Primitive.EntityUID(euid)) else e
      case If(e1, e2, e3) =>
        var e1' := substitute(e1, v, euid);
        var e2' := substitute(e2, v, euid);
        var e3' := substitute(e3, v, euid);
        If(e1', e2', e3')
      case And(e1, e2) =>
        var e1' := substitute(e1, v, euid);
        var e2' := substitute(e2, v, euid);
        And(e1', e2')
      case Or(e1, e2) =>
        var e1' := substitute(e1, v, euid);
        var e2' := substitute(e2, v, euid);
        Or(e1', e2')
      case UnaryApp(op, e1) =>
        var e1' := substitute(e1, v, euid);
        UnaryApp(op, e1')
      case BinaryApp(op, e1, e2) =>
        var e1' := substitute(e1, v, euid);
        var e2' := substitute(e2, v, euid);
        BinaryApp(op, e1', e2')
      case GetAttr(e1, a) =>
        var e1' := substitute(e1, v, euid);
        GetAttr(e1', a)
      case HasAttr(e1, a) =>
        var e1' := substitute(e1, v, euid);
        HasAttr(e1', a)
      case Set(es) =>
        var es' := seq (|es|, i requires 0 <= i < |es| => substitute(es[i], v, euid));
        Expr.Set(es')
      case Record(er) =>
        var er' := seq (|er|, i requires 0 <= i < |er| => (er[i].0, substitute(er[i].1, v, euid)));
        Expr.Record(er')
      case Call(name, args) =>
        var args' := seq (|args|, i requires 0 <= i < |args| => substitute(args[i], v, euid));
        Call(name, args')
    }
  }
}
