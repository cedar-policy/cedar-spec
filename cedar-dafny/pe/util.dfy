include "../def/std.dfy"

module pe.util {
  import opened def.std

  function {:opaque} Map<T,R>(xs: seq<T>, f: (T ~> R)): (result: seq<R>)
    requires forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
    ensures |result| == |xs|
    ensures forall i {:trigger result[i]} :: 0 <= i < |xs| ==> result[i] == f(xs[i]);
    reads set i, o | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
  {
    // This uses a sequence comprehension because it will usually be
    // more efficient when compiled, allocating the storage for |xs| elements
    // once instead of creating a chain of |xs| single element concatenations.
    seq(|xs|, i requires 0 <= i < |xs| && f.requires(xs[i])
                reads set i,o | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
    => f(xs[i]))
  }

  function CollectToSet<T,E>(rs: seq<Result<T, E>>): (result: Result<set<T>,E>) {
    if |rs| == 0 then
      Ok({})
    else
      var x :- rs[0];
      var xs :- CollectToSet(rs[1..]);
      Ok({x} + xs)
  }
}
