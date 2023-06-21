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

  lemma MapExists<T,R>(xs: seq<T>, f: (T --> R), p: (R -> bool))
    requires forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
    requires exists x | x in xs :: p(f(x))
    ensures exists y | y in Map(xs, f) :: p(y) {
    assert Map(xs, f) == seq(|xs|, i requires 0 <= i < |xs| && f.requires(xs[i]) => f(xs[i]));
    assert exists i: nat | i < |xs| :: p(f(xs[i]));
    assert exists i: nat | i < |xs| :: Map(xs, f)[i] == f(xs[i]);
    var i: nat :| i < |xs| && Map(xs, f)[i] == f(xs[i]);
  }

  lemma MapEqvFunc<A,B>(xs: seq<A>, f: (A --> B), g: (A --> B))
    requires forall i :: 0 <= i < |xs| ==> f.requires(xs[i]) && g.requires(xs[i]) && f(xs[i]) == g(xs[i])
    ensures Map(xs, f) == Map(xs, g)
  {

  }

  lemma MapCompose<T, X, Y>(es: seq<T>, f: (T --> X), g: (X -> Y))
    requires forall i :: 0 <= i < |es| ==> f.requires(es[i])
    ensures Map(Map(es, f), g) == Map(es, e requires f.requires(e) => g(f(e))) {
    if |es| == 0 {
      assume false;
    } else {
      MapCompose(es[1..], f, g);
      assert Map(Map(es, f), g) == Map([f(es[0])] + Map(es[1..], f), g) == [g(f(es[0]))] + Map(Map(es[1..], f), g);
      assert Map(es, e requires f.requires(e) => g(f(e))) == [g(f(es[0]))] + Map(es[1..], e requires f.requires(e) => g(f(e)));
    }
  }

  function CollectToSet<T,E>(rs: seq<Result<T, E>>): (result: Result<set<T>,E>) {
    if |rs| == 0 then
      Ok({})
    else
      var x :- rs[0];
      var xs :- CollectToSet(rs[1..]);
      Ok({x} + xs)
  }

  lemma CollectToSetErr<T,E>(rs: seq<Result<T, E>>)
    requires exists r | r in rs :: r.Err?
    ensures CollectToSet(rs).Err? {

  }

  lemma CollectToSetOk<T,E>(rs: seq<std.Result<T, E>>)
    requires forall r | r in rs :: r.Ok?
    ensures var res := CollectToSet(rs); res.Ok? && res.value == set x | x in rs :: x.value
  {

  }

  lemma CollectToSetWithMap<T,E, U>(rs: seq<T>, f: T--> Result<U, E>)
    requires forall r | r in rs :: f.requires(r) && f(r).Ok?
    ensures var res := CollectToSet(Map(rs, f)); res.Ok? && res.value == set x | x in rs :: f(x).value
  {
    if |rs| == 0 {

    } else {
      CollectToSetWithMap(rs[1..], f);
      assert Map(rs, f) == [f(rs[0])] + Map(rs[1..], f);
    }

  }

  function CollectToSeq<T,E>(rs: seq<Result<T, E>>): (result: Result<seq<T>,E>) {
    if |rs| == 0 then
      Ok([])
    else
      var x :- rs[0];
      var xs :- CollectToSeq(rs[1..]);
      Ok([x] + xs)
  }

  lemma CollectToSeqOk<T,E>(rs: seq<std.Result<T, E>>)
    requires forall r | r in rs :: r.Ok?
    ensures var res := CollectToSeq(rs); res.Ok? && res.value == Map(rs, (r: std.Result<T, E>) requires r.Ok? => r.value) {
    if |rs| == 0 {
      assert CollectToSeq(rs) == Ok([]);
      assert Map(rs, (r: std.Result<T, E>) requires r.Ok? => r.value) == [];
    } else {
      CollectToSeqOk(rs[1..]);
      assert CollectToSeq(rs).value == [rs[0].value] + CollectToSeq(rs[1..]).value;
      assert Map(rs, (r: std.Result<T, E>) requires r.Ok? => r.value) ==
             [rs[0].value] + Map(rs[1..], (r: std.Result<T, E>) requires r.Ok? => r.value);
    }
  }
}
