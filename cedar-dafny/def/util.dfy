/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

include "base.dfy"
include "core.dfy"

// The "util" module holds generic code that we're adopting from the Dafny
// standard library.
module def.util {
  import opened base
  import opened core

  // --------- Convert a set to a (sorted) sequence --------- //
  // Adapted from http://leino.science/papers/krml275.html

  ghost predicate IsTotalOrder<A(!new)>(R: (A, A) -> bool) {
    // connexity
    && (forall a, b :: R(a, b) || R(b, a))
       // antisymmetry
    && (forall a, b | R(a, b) && R(b, a) :: a == b)
       // transitivity
    && (forall a, b, c | R(a, b) && R(b, c) :: R(a, c))
  }

  lemma ThereIsAMinimum<A(!new)>(s: set<A>, R: (A, A) -> bool)
    requires s != {} && IsTotalOrder(R)
    ensures exists x :: x in s && forall y | y in s :: R(x, y)
  {
    var x :| x in s;
    if s == {x} {
      assert forall y | y in s :: x == y;
    } else {
      var s' := s - {x};
      assert s == s' + {x};
      ThereIsAMinimum(s', R);
      var z :| z in s' && forall y | y in s' :: R(z, y);
      if
      case R(z, x) =>
        assert s == s' + {x};
        assert z in s;
        forall y | y in s ensures R(z, y) { if y == x { assert R(z, x); } else { assert y in s'; } }
      case R(x, z) =>
        assert x in s;
        forall y | y in s ensures R(x, y) { if y == x { assert R(x, x); } else { assert y in s'; } }
    }
  }

  // Converts the given set to a sequence that is sorted according to the total
  // ordering R. Note that this is a naive way to sort a set, as it works by
  // repeatedly picking the smallest element (n^2 algorithm).
  function {: opaque } SetToSortedSeq<A(!new)>(s: set<A>, R: (A, A) -> bool): (ret: seq<A>)
    requires IsTotalOrder(R)
    ensures |s| == |ret|
    ensures forall i | 0 <= i < |ret| :: ret[i] in s
    ensures forall e | e in s :: e in ret
    ensures forall i, j | 0 <= i < j < |ret| :: R(ret[i], ret[j])
  {
    if s == {} then [] else
    ThereIsAMinimum(s, R);
    var x :| x in s && forall y | y in s :: R(x, y);
    [x] + SetToSortedSeq(s - {x}, R)
  }

  // --------- Sequence and string ordering --------- //

  predicate SeqLeq<T(==, !new)>(s1: seq<T>, s2: seq<T>, lte: (T, T) -> bool)
  {
    s1 == [] ||
    (s2 != [] &&
     if s1[0] == s2[0] then SeqLeq(s1[1..], s2[1..], lte) else lte(s1[0], s2[0]))
  }

  lemma SeqLeqIsTotalOrder<T(!new)>(seqLeq: (seq<T>, seq<T>) -> bool, lte: (T, T) -> bool)
    requires IsTotalOrder(lte)
    requires forall s1, s2 :: seqLeq(s1, s2) == SeqLeq(s1, s2, lte)
    ensures IsTotalOrder(seqLeq)
  {
    forall a, b
      ensures seqLeq(a, b) || seqLeq(b, a)
    { SeqLeqConnexity(a, b, lte); }
    forall a, b
      ensures seqLeq(a, b) && seqLeq(b, a) ==> a == b
    { SeqLeqAntisymmetry(a, b, lte); }
    forall a, b, c
      ensures seqLeq(a, b) && seqLeq(b, c) ==> seqLeq(a, c)
    { SeqLeqTransitivity(a, b, c, lte); }
  }

  lemma SeqLeqConnexity<T(!new)>(s1: seq<T>, s2: seq<T>, lte: (T, T) -> bool)
    requires IsTotalOrder(lte)
    ensures SeqLeq(s1, s2, lte) || SeqLeq(s2, s1, lte)
  {}

  lemma SeqLeqAntisymmetry<T(!new)>(s1: seq<T>, s2: seq<T>, lte: (T, T) -> bool)
    requires IsTotalOrder(lte)
    ensures SeqLeq(s1, s2, lte) && SeqLeq(s2, s1, lte) ==> s1 == s2
  {
    if s1 != [] && s2 != [] {
      var h1, h2 := s1[0], s2[0];
      if h1 == h2 {
        SeqLeqAntisymmetry(s1[1..], s2[1..], lte);
      }
    }
  }

  lemma SeqLeqTransitivity<T(!new)>(s1: seq<T>, s2: seq<T>, s3: seq<T>, lte: (T, T) -> bool)
    requires IsTotalOrder(lte)
    ensures SeqLeq(s1, s2, lte) && SeqLeq(s2, s3, lte) ==> SeqLeq(s1, s3, lte)
  {
    if SeqLeq(s1, s2, lte) && SeqLeq(s2, s3, lte) {
      if s1 != [] && s2 != [] && s3 != [] {
        var h1, h2, h3 := s1[0], s2[0], s3[0];
        if h1 == h2 == h3 {
          SeqLeqTransitivity(s1[1..], s2[1..], s3[1..], lte);
        } else {
          assert lte(h1, h2) && lte(h2, h3) && lte(h1, h3);
        }
      }
    }
  }

  predicate StringLeq(s1: string, s2: string)
  {
    SeqLeq(s1, s2, (c1: char, c2: char) => c1 <= c2)
  }

  lemma StringLeqIsTotalOrder()
    ensures IsTotalOrder(StringLeq)
  {
    SeqLeqIsTotalOrder(StringLeq, (c1: char, c2: char) => c1 <= c2);
  }

  lemma SeqAddInequality<T>(s1: seq<T>, t1: T, s2: seq<T>, t2: T)
    requires s1 != s2 || t1 != t2
    ensures s1 + [t1] != s2 + [t2]
  {
    if s1 == s2 {
      assert t1 != t2;
      var len := |s1|;
      assert (s1 + [t1])[len] != (s2 + [t2])[len];
    } else if |s1| == |s2| {
      var i :| 0 <= i < |s1| && s1[i] != s2[i];
      assert (s1 + [t1])[i] != (s2 + [t2])[i];
    } else {
      assert |s1 + [t1]| != |s2 + [t2]|;
    }
  }

  // --------- Name and entity type ordering --------- //

  predicate IdLeq(id1: Id, id2: Id) {
    StringLeq(id1.id, id2.id)
  }

  predicate PathLeq(p1: seq<Id>, p2: seq<Id>)
  {
    SeqLeq(p1, p2, IdLeq)
  }

  predicate NameLeq(n1: Name, n2: Name)
  {
    PathLeq(n1.path + [n1.id], n2.path + [n2.id])
  }

  predicate EntityTypeLeq(ety1: EntityType, ety2: EntityType)
  {
    NameLeq(ety1.id, ety2.id)
  }

  lemma EntityTypeLeqIsTotalOrder()
    ensures IsTotalOrder(EntityTypeLeq)
  {
    NameLeqIsTotalOrder();
  }

  lemma NameLeqIsTotalOrder()
    ensures IsTotalOrder(NameLeq)
  {
    forall n1, n2: Name | n1 != n2
      ensures n1.path + [n1.id] != n2.path + [n2.id]
    {
      assert n1.path != n2.path || n1.id != n2.id;
      SeqAddInequality(n1.path, n1.id, n2.path, n2.id);
    }
    PathLeqIsTotalOrder();
  }

  lemma PathLeqIsTotalOrder()
    ensures IsTotalOrder(PathLeq)
  {
    StringLeqIsTotalOrder();
    assert IsTotalOrder(PathLeq) by {
      SeqLeqIsTotalOrder(PathLeq, IdLeq);
    }
  }

  // KeyExists and LastOfKey are helpers about association lists that are used in
  // validation.dfy, so we lift them here.
  // We use these as an abbreviation for the quantifier alternation:
  // exists i :: 0 <= i < |es| && (forall j :: i < j < |es| => ...)
  // This helps dafny prove some of our lemmas about record evaluation and validation.
  ghost predicate KeyExists<K,V>(k: K, es: seq<(K,V)>) {
    exists i :: 0 <= i < |es| && es[i].0 == k
  }

  opaque ghost function LastOfKey<K,V>(k: K, es: seq<(K,V)>): (res: V)
    requires KeyExists(k,es)
    ensures exists i :: 0 <= i < |es| && es[i].0 == k && es[i].1 == res && (forall j | i < j < |es| :: es[j].0 != k)
  {
    if (es[0].0 == k && (forall j | 0 < j < |es| :: es[j].0 != k)) then es[0].1 else LastOfKey(k,es[1..])
  }
}
