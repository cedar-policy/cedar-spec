include "../base.dfy"

module def.ext.fun {

  import opened base

  datatype ExtFun<!T(!new,==)> = ExtFun(fun: seq<T> -> Result<T>)

  datatype Coercions<!E(!new,==), !T(!new,==)> =
    Coercions(
      Bool:   Coerce<bool, T>,
      Int:    Coerce<int, T>,
      String: Coerce<string, T>,
      Ext:    Coerce<E, T>)
  {
    ghost predicate wellFormed() {
      Bool.wellFormed() &&
      Int.wellFormed() &&
      String.wellFormed() &&
      Ext.wellFormed()
    }

    static function compose<W(!new,==)>(c: Coerce<E, W>, cs: Coercions<W, T>): (res: Coercions<E, T>)
      ensures (c.wellFormed() && cs.wellFormed()) ==> res.wellFormed()
    {
      Coercions(cs.Bool, cs.Int, cs.String, Coerce.compose(c, cs.Ext))
    }

    // Convenience functions for calling coercion wrapper.
    function fromBool(arg: bool):     T { Bool.wrap(arg) }
    function fromInt(arg: int):       T { Int.wrap(arg) }
    function fromString(arg: string): T { String.wrap(arg) }
    function fromExt(arg: E):         T { Ext.wrap(arg)}

    function toBool(arg: T):   Result<bool>   { Bool.unwrap(arg) }
    function toInt(arg: T):    Result<int>    { Int.unwrap(arg) }
    function toString(arg: T): Result<string> { String.unwrap(arg) }
    function toExt(arg: T):    Result<E>      { Ext.unwrap(arg) }
  }

  function checkArity<T>(args: seq<T>, expected: nat): (res: UnitResult)
    ensures res.Ok? ==> |args| == expected
  {
    if |args| == expected
    then Ok(())
    else Err(ArityMismatchError)
  }

  function checkUnary<B(==,!new), W(==,!new)>(args: seq<W>, expected: Coerce<B, W>): (res: Result<B>)
    ensures
      res.Ok? <==>
      (|args| == 1 && expected.unwrap(args[0]).Ok?)
  {
    var _ :- checkArity(args, 1);
    var a0 :- expected.unwrap(args[0]);
    Ok(a0)
  }

  function checkBinary<B(==,!new), W(==,!new)>(args: seq<W>, expected: Coerce<B, W>): (res: Result<(B, B)>)
    ensures
      res.Ok? <==>
      (|args| == 2 && expected.unwrap(args[0]).Ok? && expected.unwrap(args[1]).Ok?)
  {
    var _ :- checkArity(args, 2);
    var a0 :- expected.unwrap(args[0]);
    var a1 :- expected.unwrap(args[1]);
    Ok((a0, a1))
  }


}
