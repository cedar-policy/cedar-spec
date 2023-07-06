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

include "../../def/all.dfy"

// This module contains lemmas stating the behaviors of Cedar evaluator.
module eval.basic {
  import opened def.base
  import opened def.core
  import opened def.engine
  import opened def.util

  lemma EntityInOrEqEntitySemantics(x1: Expr, e1: EntityUID, x2: Expr, e2: EntityUID, E: Evaluator)
    requires E.interpret(x1) == Ok(Value.EntityUID(e1))
    requires E.interpret(x2) == Ok(Value.EntityUID(e2))
    requires
      E.interpret(BinaryApp(BinaryOp.In, x1, x2)) == Ok(Value.TRUE) ||
      E.interpret(BinaryApp(BinaryOp.Eq, x1, x2)) == Ok(Value.TRUE)
    ensures E.entityInEntity(e1, e2)
  { }

  lemma AndSemantics(e1: Expr, e2: Expr, E: Evaluator)
    requires E.interpret(And(e1, e2)) == Ok(Value.TRUE)
    ensures E.interpret(e1) == Ok(Value.TRUE)
    ensures E.interpret(e2) == Ok(Value.TRUE)
  { }

  lemma RecordSemanticsOkImpliesAllOk(es: seq<(Attr, Expr)>, E: Evaluator)
    requires E.interpretRecord(es).Ok?
    ensures forall i :: 0 <= i < |es| ==> es[i].0 in E.interpretRecord(es).value.Keys && E.interpret(es[i].1).Ok?
  {
    if es == [] {

    } else if E.interpret(es[0].1).Ok? && E.interpretRecord(es[1..]).Ok? {

    } else {
      assert E.interpretRecord(es).Err?;
    }
  }

  lemma RecordSemanticsOkAttrs(es: seq<(Attr, Expr)>, E: Evaluator)
    requires E.interpretRecord(es).Ok?
    ensures E.interpretRecord(es).value.Keys == set e | e in es :: e.0
  {
    if es != [] {
      RecordSemanticsOkAttrs(es[1..], E);
      var rec' := E.interpretRecord(es[1..]).value;
      if es[0].0 in rec'.Keys {
        assert E.interpretRecord(es).value == rec';
        assert (set e | e in es :: e.0) == (set e | e in es[1..] :: e.0);
      } else {
        assert E.interpretRecord(es).value == rec'[es[0].0 := E.interpret(es[0].1).value];
        assert (set e | e in es :: e.0) == (set e | e in es[1..] :: e.0) + {es[0].0};
      }
    }
  }

  lemma RecordSemanticsOkLastofKey(es: seq<(Attr, Expr)>, E: Evaluator)
    requires E.interpretRecord(es).Ok?
    ensures forall k | k in E.interpretRecord(es).value.Keys :: KeyExists(k,es) && E.interpret(LastOfKey(k,es)) == base.Ok(E.interpretRecord(es).value[k])
  {
    if |es| == 0 {
    } else {
      if E.interpret(es[0].1).Ok? && E.interpretRecord(es[1..]).Ok? {
        var rec' := E.interpretRecord(es[1..]).value;
        RecordSemanticsOkLastofKey(es[1..], E);
        if es[0].0 in rec'.Keys {
          assert E.interpretRecord(es).value == rec';
        } else {
          RecordSemanticsOkAttrs(es[1..], E);
          assert LastOfKey(es[0].0, es) == es[0].1;
        }
      } else {
        assert E.interpretRecord(es).Err?;
      }
    }
  }

  lemma RecordSemanticsOk(es: seq<(Attr,Expr)>, E: Evaluator)
    requires E.interpretRecord(es).Ok?
    ensures forall i :: 0 <= i < |es| ==> es[i].0 in E.interpretRecord(es).value.Keys && E.interpret(es[i].1).Ok?
    ensures forall k | k in E.interpretRecord(es).value.Keys :: KeyExists(k,es) && E.interpret(LastOfKey(k,es)) == base.Ok(E.interpretRecord(es).value[k])
  {
    RecordSemanticsOkImpliesAllOk(es, E);
    RecordSemanticsOkLastofKey(es, E);
  }

  lemma RecordSemanticsErr(es: seq<(Attr,Expr)>, E: Evaluator)
    requires E.interpretRecord(es).Err?
    ensures exists i :: 0 <= i < |es| && E.interpret(es[i].1) == base.Err(E.interpretRecord(es).error) && (forall j | 0 <= j < i :: E.interpret(es[j].1).Ok?)
  {}

  lemma SetSemantics(es: seq<Expr>, E: Evaluator)
    ensures E.interpretSet(es).Ok? ==> forall v | v in E.interpretSet(es).value :: exists i :: 0 <= i < |es| && E.interpret(es[i]) == base.Ok(v)
    ensures (forall e | e in es :: E.interpret(e).Ok?) ==> E.interpretSet(es).Ok?
    ensures (exists i :: 0 <= i < |es| && E.interpret(es[i]).Err?) ==> E.interpretSet(es).Err?
    ensures E.interpretSet(es).Err? <==> exists i :: 0 <= i < |es| && E.interpret(es[i]).Err? && (forall j | 0 <= j < i :: E.interpret(es[j]).Ok?);
    ensures E.interpretSet(es).Err? ==> exists i :: 0 <= i < |es| && E.interpret(es[i]).Err? && E.interpret(es[i]).error == E.interpretSet(es).error && (forall j | 0 <= j < i :: E.interpret(es[j]).Ok?);
  {}

  lemma ListSemanticsOk(es: seq<Expr>, E: Evaluator)
    requires forall i | 0 <= i < |es| :: E.interpret(es[i]).Ok?
    ensures E.interpretList(es).Ok?
    ensures |E.interpretList(es).value| == |es|
    ensures forall i | 0 <= i < |es| :: E.interpret(es[i]) == base.Ok(E.interpretList(es).value[i])
  {
    ListSemantics(es, E);
  }

  lemma ListSemanticsErr(es: seq<Expr>, E: Evaluator)
    requires exists i | 0 <= i < |es| :: E.interpret(es[i]).Err?
    ensures E.interpretList(es).Err?
    ensures exists i :: 0 <= i < |es| && E.interpret(es[i]).Err? && (forall j | 0 <= j < i :: E.interpret(es[j]).Ok?) && E.interpret(es[i]).error == E.interpretList(es).error
  {
    ListSemantics(es, E);
  }

  lemma ListSemantics(es: seq<Expr>, E: Evaluator)
    ensures E.interpretList(es).Ok? ==>
              (|E.interpretList(es).value| == |es| &&
               forall i | 0 <= i < |es| :: E.interpret(es[i]) == base.Ok(E.interpretList(es).value[i]))
    ensures (forall e | e in es :: E.interpret(e).Ok?) ==> E.interpretList(es).Ok?
    ensures (exists i :: 0 <= i < |es| && E.interpret(es[i]).Err?) ==> E.interpretList(es).Err?
    ensures E.interpretList(es).Err? <==> exists i :: 0 <= i < |es| && E.interpret(es[i]).Err? && (forall j | 0 <= j < i :: E.interpret(es[j]).Ok?)
    ensures E.interpretList(es).Err? ==> exists i :: 0 <= i < |es| && E.interpret(es[i]).Err? && E.interpret(es[i]).error == E.interpretList(es).error && (forall j | 0 <= j < i :: E.interpret(es[j]).Ok?)
  {}

}
