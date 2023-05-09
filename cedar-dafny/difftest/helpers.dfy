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

include "../def/std.dfy"

module difftest.helpers {
  // This module contains helper code for differential testing that isn't
  // specific to the part of the definitional implementation being tested.

  import opened def.std

  // ----- Dafny utilities not specific to Cedar -----

  function mapSeq<A, B>(f: A --> B, s: seq<A>): seq<B>
    requires forall i | 0 <= i < |s| :: f.requires(s[i]) {
    seq(|s|, i requires 0 <= i < |s| => f(s[i]))
  }

  function mapMapKeys<K1, K2, V>(
    keyFn: K1 -> K2, m: map<K1, V>): map<K2, V>
    requires forall x1, x2 | x1 in m.Keys && x2 in m.Keys :: keyFn(x1) == keyFn(x2) ==> x1 == x2 {
    var newKeys := set k | k in m.Keys :: keyFn(k);
    map nk | nk in newKeys ::
      (var k :| k in (set k1 | k1 in m.Keys && keyFn(k1) == nk); m[k])
  }

  method setToSequenceUnordered<T>(st: set<T>) returns (sq: seq<T>) {
    var st1 := st;
    sq := [];
    while st1 != {} {
      var x :| x in st1;
      sq := sq + [x];
      st1 := st1 - {x};
    }
  }

  function singleElementOfSet<T>(s: set<T>): (x: T)
    requires |s| == 1
    ensures s == {x}
  {
    var x :| x in s;
    assert |s - {x}| == 0;
    x
  }

  method flattenSet_method<T>(s: set<set<T>>) returns (r: set<T>) {
    var s1 := s;
    r := {};
    while s1 != {} {
      var x :| x in s1;
      r := r + x;
      s1 := s1 - {x};
    }
  }

  function flattenSet<T(!new)>(s: set<set<T>>): (r: set<T>)
    ensures forall x | x in r :: exists y :: x in y && y in s
    ensures forall x, y | x in y && y in s :: x in r
  {
    set x, y | x in y && y in s :: x
  }

  function printFromFunction<T>(x: T): () {
    ()
  } by method {
    print x;
    return ();
  }

  // ----- Idealized JSON data structure -----
  //
  // This is used as a narrow interface to marshal data
  // between Dafny-generated target code and handwritten target code.

  datatype Json =
    JsonNull |
    JsonBool(b: bool) |
    JsonInt(i: int) |
    JsonString(s: string) |
    JsonArray(a: seq<Json>) |
    JsonObject(o: map<string, Json>)
  {
    function JsonAsString(): string {
      match this {
        case JsonNull => "null"
        case JsonBool(true) => "true"
        case JsonBool(false) => "false"
        case JsonInt(_) => "integer"
        case JsonString(s) => "\"" + s + "\""
        case JsonArray(_) => "array"
        case JsonObject(o) => if |o.Keys| == 0 then
          "empty object"
        else if |o.Keys| == 1 then
          "object with single field " + singleElementOfSet(o.Keys)
        else
          "object with 2 or more fields"
      }
    }
  }

  // ----- Err and Result types for data structure conversion -----

  /* Here and below, "FromProd" refers to conversion from a JSON dump of the
   * production data structures to the definitional data structures. That is, we
   * are both deserializing the JSON and handling the the differences between
   * the production and definitional data structures, and either of those tasks
   * can raise a FromProdErr.
   *
   * We choose to interleave the code to perform the two tasks rather than
   * performing all the deserialization before all the production/definitional
   * conversion. This saves us the work of maintaining a separate set of Dafny
   * data structures that just mirror the production data structures. The
   * downside is that it's less obvious where the production/definitional
   * conversions are occurring, and understanding these conversions is helpful
   * in understanding what kind of assurance we're getting from differential
   * testing.
   */

  /* An UnexpectedFromProdErr indicates a problem that should never occur if DRT
   * is working correctly (and in particular, input generation is limited to
   * features supported by both the definitional and production
   * implementations).
   */

  datatype FromProdErr = UnexpectedFromProdErr(desc: string) | InvalidAttrVal
  type FromProdResult<T> = std.Result<T, set<FromProdErr>>

  // ----- Helpers to extract pieces of data from JSON -----

  function getJsonBool(j: Json): FromProdResult<bool> {
    match j {
      case JsonBool(b) => Ok(b)
      case _ => Err({UnexpectedFromProdErr("expected bool, got " + j.JsonAsString())})
    }
  }
  function getJsonInt(j: Json): FromProdResult<int> {
    match j {
      case JsonInt(i) => Ok(i)
      case _ => Err({UnexpectedFromProdErr("expected int, got " + j.JsonAsString())})
    }
  }
  function getJsonString(j: Json): FromProdResult<string> {
    match j {
      case JsonString(s) => Ok(s)
      case _ => Err({UnexpectedFromProdErr("expected string, got " + j.JsonAsString())})
    }
  }
  function getJsonArray(j: Json): FromProdResult<seq<Json>> {
    match j {
      case JsonArray(a) => Ok(a)
      case _ => Err({UnexpectedFromProdErr("expected array, got " + j.JsonAsString())})
    }
  }
  function getJsonObject(j: Json): FromProdResult<map<string, Json>> {
    match j {
      case JsonObject(o) => Ok(o)
      case _ => Err({UnexpectedFromProdErr("expected object, got " + j.JsonAsString())})
    }
  }
  function getJsonField(j: Json, f: string): (r: FromProdResult<Json>)
    ensures r.Ok? ==> r.value < j
  {
    var o :- getJsonObject(j);
    if f in o.Keys then
      Ok(o[f])
    else
      Err({UnexpectedFromProdErr("getJsonField: requested key " + f + " doesn't exist")})
  }

  /* Unpack the default Serde serialization of a Rust "enum" value into a tuple:
   * (variant tag, body).
   *
   * If the Rust enum constructor has no fields, Serde just outputs the tag as a
   * string. If the constructor has at least one field, Serde generates a JSON
   * object with a single field, named after the tag, whose value is a JSON
   * object containing the original fields. unpackJsonSum accepts both formats,
   * and in the first case, it returns jsonEmptyObject as the body for
   * consistency.
   *
   * When `j` is a JsonString, no matter what value we return as the body, it
   * complicates the termination proof for callers that recurse on the body
   * because we won't have `body < j`. For exprFromProdJson, we're OK because
   * exprFromProdJson never recurses directly on `body` but only on a proper
   * subterm of it, and jsonEmptyObject has no proper subterms that are Json
   * values. But Dafny can't seem to prove the latter fact directly, so we give
   * it a little help by including a `jsonEmptyObject` special case in
   * `deserializerAcceptsSubterms`. Two alternative designs that would avoid the
   * problem would be to (1) put the body in an option type or (2) take
   * advantage of the fact that none of our recursive datatypes currently
   * have any constructors that take no fields and have them use a separate
   * version of unpackJsonSum that doesn't accept JsonStrings. But the current
   * design seems nicer as long as proving termination doesn't become too much
   * of a hassle.
   */
  function unpackJsonSum(j: Json): (r: FromProdResult<(string, Json)>)
    ensures r.Ok? ==> r.value.1 == jsonEmptyObject || r.value.1 < j
  {
    match j {
      case JsonString(tag) =>
        Ok((tag, jsonEmptyObject))
      case JsonObject(o) =>
        if |o.Keys| == 1 then
          var k := singleElementOfSet(o.Keys);
          Ok((k, o[k]))
        else
          var _ := printFromFunction(j);
          var _ := printFromFunction("\n");
          Err({UnexpectedFromProdErr("unpackJsonSum: expected exactly one key, got either zero or multiple")})
      case _ => Err({UnexpectedFromProdErr("unpackJsonSum: expected an object or a string")})
    }
  }

  // ----- Helpers to convert composite data structures -----
  //
  // These do not interact directly with the `Json` datatype but are often used
  // with callbacks that do.

  function mapMapValuesFromProd<K, V1, V2>(
    valueFn: V1 -> FromProdResult<V2>, m: map<K, V1>): (res: FromProdResult<map<K, V2>>)
    ensures (forall k | k in m.Keys :: valueFn(m[k]).Ok?) ==> res.Ok?
    ensures res.Ok? ==> res.value.Keys == m.Keys
  {
    var m1 := map k | k in m.Keys :: valueFn(m[k]);
    if forall k | k in m1.Keys :: m1[k].Ok? then
      Ok(map k | k in m1.Keys :: m1[k].value)
    else
      Err(flattenSet(set k | k in m1.Keys && m1[k].Err? :: m1[k].error))
  }

  function mapMapKeysFromProd<K1, K2, V>(
    keyFn: K1 -> FromProdResult<K2>, m: map<K1, V>): FromProdResult<map<K2, V>>
    requires forall x1, x2 | x1 in m.Keys && x2 in m.Keys :: keyFn(x1) == keyFn(x2) ==> x1 == x2
  {
    var newKeys := set k | k in m.Keys :: keyFn(k);
    if forall k | k in newKeys :: k.Ok? then
      var newKeysOks := set k | k in newKeys :: k.value;
      Ok(map nk | nk in newKeysOks ::
           (var k :| k in (set k1 | k1 in m.Keys && keyFn(k1) == Ok(nk)); m[k]))
    else
      Err(flattenSet(set k | k in newKeys && k.Err? :: k.error))
  }

  function mapSeqFromProd<A, B>(f: A --> FromProdResult<B>, s: seq<A>): FromProdResult<seq<B>>
    requires forall i | 0 <= i < |s| :: f.requires(s[i]) {
    var s1 := mapSeq(f, s);
    if forall i | 0 <= i < |s1| :: s1[i].Ok? then
      Ok(mapSeq((rb: FromProdResult<B>) requires rb.Ok? => rb.value, s1))
    else
      Err(flattenSet(set i | 0 <= i < |s1| && s1[i].Err? :: s1[i].error))
  }

  function mapSetFromProd<A, B>(f: A --> FromProdResult<B>, s: seq<A>): FromProdResult<set<B>>
    requires forall i | 0 <= i < |s| :: f.requires(s[i]) {
    var s1 :- mapSeqFromProd(f, s);
    Ok(set i | 0 <= i < |s1| :: s1[i])
  }

  function mapFromEntriesProd<K, V>(entries: seq<(K, V)>): FromProdResult<map<K, V>> {
    if (forall i, j | 0 <= i < |entries| && 0 <= j < |entries| ::
          entries[i].0 == entries[j].0 ==> i == j) then
      var keys := set i | 0 <= i < |entries| :: entries[i].0;
      Ok(map k | k in keys ::
           (var i :| i in (set i1 | 0 <= i1 < |entries| && entries[i1].0 == k); entries[i].1))
    else
      Err({UnexpectedFromProdErr("duplicate key")})
  }

  // ----- "Serialization combinator" library -----
  //
  // These functions factor out common patterns of deserialization logic so they
  // can be performed with less boilerplate than by using lower-level functions
  // such as getJson* directly.
  //
  // This library is agnostic to the meaning of the Dafny datatypes and hence is
  // agnostic to whether callers are performing production/definitional
  // conversion under the guise of deserialization (see the comment on
  // FromProdErr above), as they sometimes are.
  //
  // The sets of Dafny datatypes that we need to convert _to_ and _from_ JSON
  // are currently disjoint. For conversion to JSON, handwritten code is already
  // reasonably clean and a library wouldn't help very much. Thus, this library
  // currently only supports conversion from JSON, which is the direction that
  // has all the messy error checks that we want to factor out. In the future,
  // if we need to convert the same datatypes in both directions, then it might
  // be beneficial to enhance the library to support sharing per-datatype code
  // between the two directions.
  //
  // API overview:
  //
  // - `deserializeFoo(j, ...)` extracts the top-level structure of a "foo" from
  //   the JSON `j` and then uses one or more caller-provided callbacks to
  //   finish the conversion of the retrieved sub-items, as applicable. For
  //   example, `deserializeSeq(j, ed)` converts a JSON array to a Dafny `seq`,
  //   using the callback `ed` ("element deserializer") to convert each element
  //   of the array.
  //
  // - `fooDeserializer(...)` is a shortcut for `j => deserializeFoo(j, ...)`.
  //   `fooDeserializer` typically results in less boilerplate than
  //   `deserializeFoo` because it can be passed directly as a callback to
  //   another `deserializeBar` or `barDeserializer` function. The exception is
  //   when the data structure is recursive: `deserializeFoo(j, ...)` supports
  //   partial callbacks that only accept inputs smaller than `j` (see
  //   `deserializerAcceptsSubterms`), while it's unworkable to implement an
  //   analogous thing for `fooDeserializer`.

  type Deserializer<T> = Json -> FromProdResult<T>

  // A deserializer with a precondition. Preconditions should be used only to
  // verify termination with recursive data structures and not to rule out
  // invalid input, which should still be reported by returning a FromProdErr.
  type PartialDeserializer<T> = Json --> FromProdResult<T>

  const jsonEmptyObject := JsonObject(map[])

  ghost predicate deserializerAcceptsSubterms<T>(d: PartialDeserializer<T>, j: Json) {
    // See the explanation in unpackJsonSum regarding jsonEmptyObject.
    j == jsonEmptyObject || forall jr | jr < j :: d.requires(jr)
  }

  function boolDeserializer<T>(cons: bool -> FromProdResult<T>): Deserializer<T> {
    j => (var b :- getJsonBool(j); cons(b))
  }
  function intDeserializer<T>(cons: int -> FromProdResult<T>): Deserializer<T> {
    j => (var i :- getJsonInt(j); cons(i))
  }
  function stringDeserializer<T>(cons: string -> FromProdResult<T>): Deserializer<T> {
    j => (var s :- getJsonString(j); cons(s))
  }

  function deserializeField<F>(
    j: Json, fn: string, fd: PartialDeserializer<F>): FromProdResult<F>
    requires deserializerAcceptsSubterms(fd, j)
  {
    var jf :- getJsonField(j, fn); fd(jf)
  }

  function deserializeObj1Field<T, F1>(
    j: Json,
    fn1: string, fd1: Deserializer<F1>,
    cons: F1 -> FromProdResult<T>): FromProdResult<T>
  {
    var f1 :- deserializeField(j, fn1, fd1);
    cons(f1)
  }
  function objDeserializer1Field<T, F1>(
    fn1: string, fd1: Deserializer<F1>,
    cons: F1 -> FromProdResult<T>): Deserializer<T>
  {
    j => deserializeObj1Field(j, fn1, fd1, cons)
  }
  function deserializeObj2Fields<T, F1, F2>(
    j: Json,
    fn1: string, fd1: PartialDeserializer<F1>,
    fn2: string, fd2: PartialDeserializer<F2>,
    cons: (F1, F2) -> FromProdResult<T>): FromProdResult<T>
    requires deserializerAcceptsSubterms(fd1, j) && deserializerAcceptsSubterms(fd2, j)
  {
    // If we wanted, we could restructure this code (and other code like it) to
    // attempt deserialization of f2 even if f1 fails in order to report as many
    // errors as possible in a single pass. Currently, we're satisfied to get
    // one error at a time and don't see a need to make this code any more
    // complex.
    var f1 :- deserializeField(j, fn1, fd1);
    var f2 :- deserializeField(j, fn2, fd2);
    cons(f1, f2)
  }
  function objDeserializer2Fields<T, F1, F2>(
    fn1: string, fd1: Deserializer<F1>,
    fn2: string, fd2: Deserializer<F2>,
    cons: (F1, F2) -> FromProdResult<T>): Deserializer<T>
  {
    j => deserializeObj2Fields(j, fn1, fd1, fn2, fd2, cons)
  }
  function deserializeObj3Fields<T, F1, F2, F3>(
    j: Json,
    fn1: string, fd1: PartialDeserializer<F1>,
    fn2: string, fd2: PartialDeserializer<F2>,
    fn3: string, fd3: PartialDeserializer<F3>,
    cons: (F1, F2, F3) -> FromProdResult<T>): FromProdResult<T>
    requires deserializerAcceptsSubterms(fd1, j) && deserializerAcceptsSubterms(fd2, j)
             && deserializerAcceptsSubterms(fd3, j)
  {
    var f1 :- deserializeField(j, fn1, fd1);
    var f2 :- deserializeField(j, fn2, fd2);
    var f3 :- deserializeField(j, fn3, fd3);
    cons(f1, f2, f3)
  }
  function objDeserializer3Fields<T, F1, F2, F3>(
    fn1: string, fd1: Deserializer<F1>,
    fn2: string, fd2: Deserializer<F2>,
    fn3: string, fd3: Deserializer<F3>,
    cons: (F1, F2, F3) -> FromProdResult<T>): Deserializer<T>
  {
    j => deserializeObj3Fields(j, fn1, fd1, fn2, fd2, fn3, fd3, cons)
  }
  function deserializeObj5Fields<T, F1, F2, F3, F4, F5>(
    j: Json,
    fn1: string, fd1: PartialDeserializer<F1>,
    fn2: string, fd2: PartialDeserializer<F2>,
    fn3: string, fd3: PartialDeserializer<F3>,
    fn4: string, fd4: PartialDeserializer<F4>,
    fn5: string, fd5: PartialDeserializer<F5>,
    cons: (F1, F2, F3, F4, F5) -> FromProdResult<T>): FromProdResult<T>
    requires deserializerAcceptsSubterms(fd1, j) && deserializerAcceptsSubterms(fd2, j)
             && deserializerAcceptsSubterms(fd3, j) && deserializerAcceptsSubterms(fd4, j)
             && deserializerAcceptsSubterms(fd5, j)
  {
    var f1 :- deserializeField(j, fn1, fd1);
    var f2 :- deserializeField(j, fn2, fd2);
    var f3 :- deserializeField(j, fn3, fd3);
    var f4 :- deserializeField(j, fn4, fd4);
    var f5 :- deserializeField(j, fn5, fd5);
    cons(f1, f2, f3, f4, f5)
  }
  function objDeserializer5Fields<T, F1, F2, F3, F4, F5>(
    fn1: string, fd1: Deserializer<F1>,
    fn2: string, fd2: Deserializer<F2>,
    fn3: string, fd3: Deserializer<F3>,
    fn4: string, fd4: Deserializer<F4>,
    fn5: string, fd5: Deserializer<F5>,
    cons: (F1, F2, F3, F4, F5) -> FromProdResult<T>): Deserializer<T>
  {
    j => deserializeObj5Fields(j, fn1, fd1, fn2, fd2, fn3, fd3, fn4, fd4, fn5, fd5, cons)
  }

  function deserializeTuple2Elts<T, E1, E2>(
    j: Json,
    ed1: PartialDeserializer<E1>,
    ed2: PartialDeserializer<E2>,
    cons: (E1, E2) -> FromProdResult<T>): FromProdResult<T>
    requires deserializerAcceptsSubterms(ed1, j) && deserializerAcceptsSubterms(ed2, j)
  {
    var tuple :- getJsonArray(j);
    var (j1, j2) :-
      if |tuple| == 2
      then Ok((tuple[0], tuple[1]))
      else Err({UnexpectedFromProdErr("expected tuple of size 2")});
    var e1 :- ed1(j1);
    var e2 :- ed2(j2);
    cons(e1, e2)
  }
  function tupleDeserializer2Elts<T, E1, E2>(
    ed1: Deserializer<E1>,
    ed2: Deserializer<E2>,
    cons: (E1, E2) -> FromProdResult<T>): Deserializer<T> {
    j => deserializeTuple2Elts(j, ed1, ed2, cons)
  }

  function deserializeSeq<T>(j: Json, ed: PartialDeserializer<T>): FromProdResult<seq<T>>
    requires deserializerAcceptsSubterms(ed, j)
  {
    var ja :- getJsonArray(j);
    var sr := mapSeq(ed, ja);
    if forall i | 0 <= i < |sr| :: sr[i].Ok?
    then Ok(mapSeq((er: FromProdResult<T>) requires er.Ok? => er.value, sr))
    else
      // Work around a bug in the Dafny to Java compiler
      // (https://github.com/dafny-lang/dafny/issues/3320).
      //Err(set i, err | 0 <= i < |sr| && sr[i].Err? && err in sr[i].error :: err)
      var serrs := mapSeq((r: FromProdResult<T>) => if r.Err? then r.error else {}, sr);
      Err(set i, err | 0 <= i < |sr| && err in serrs[i] :: err)
  }
  function seqDeserializer<T>(ed: Deserializer<T>): Deserializer<seq<T>> {
    j => deserializeSeq(j, ed)
  }

  function deserializeSet<T>(j: Json, ed: PartialDeserializer<T>): FromProdResult<set<T>>
    requires deserializerAcceptsSubterms(ed, j)
  {
    var sq :- deserializeSeq(j, ed);
    Ok(set e | e in sq)
  }
  function setDeserializer<T>(ed: Deserializer<T>): Deserializer<set<T>> {
    j => deserializeSet(j, ed)
  }

  function deserializeMap<V>(j: Json, ed: PartialDeserializer<V>): FromProdResult<map<string,V>>
    requires deserializerAcceptsSubterms(ed, j)
  {
    var o :- getJsonObject(j);
    // copied from mapMapValuesFromProd, which is not defined over partial funcs
    var m := map k | k in o.Keys :: ed(o[k]);
    if forall k | k in m.Keys :: m[k].Ok? then
      Ok(map k | k in m.Keys :: m[k].value)
    else
      Err(flattenSet(set k | k in m.Keys && m[k].Err? :: m[k].error))
  }
  function mapDeserializer<V>(ed: Deserializer<V>): Deserializer<map<string,V>> {
    j => deserializeMap(j, ed)
  }

  function deserializeSum<T>(j: Json, consMap: map<string, PartialDeserializer<T>>): FromProdResult<T>
    requires forall t | t in consMap ::
               deserializerAcceptsSubterms(consMap[t], j) && consMap[t].requires(jsonEmptyObject)
  {
    var (tag, body) :- unpackJsonSum(j);
    if tag in consMap then
      consMap[tag](body)
    else
      Err({UnexpectedFromProdErr("deserializeSum case: " + tag)})
  }
  function sumDeserializer<T>(consMap: map<string, Deserializer<T>>): Deserializer<T> {
    j => deserializeSum(j, consMap)
  }

  // `bodyDeserializer` can be convenient for a variant of a sum type where you
  // have an existing deserializer for the body and the only follow-up you need
  // is to call the constructor of the sum type. `bodyDeserializer` saves only
  // a small amount of code but helps maintain the declarative style. We don't
  // provide a `deserializeBody` counterpart because its benefit would be even
  // smaller and it wouldn't be worth using.
  function bodyDeserializer<T, B>(bd: Deserializer<B>, cons: B -> FromProdResult<T>): Deserializer<T> {
    j => (var b :- bd(j); cons(b))
  }

  // Specialization of `deserializeSum` where none of the constructors have any
  // fields, so we can just specify a T for each constructor and save some
  // boilerplate.
  function deserializeEnum<T>(j: Json, valueMap: map<string, T>): FromProdResult<T> {
    var tag :- getJsonString(j);
    if tag in valueMap then
      Ok(valueMap[tag])
    else
      Err({UnexpectedFromProdErr("deserializeEnum case: " + tag)})
  }
  function enumDeserializer<T>(valueMap: map<string, T>): Deserializer<T> {
    j => deserializeEnum(j, valueMap)
  }

}
