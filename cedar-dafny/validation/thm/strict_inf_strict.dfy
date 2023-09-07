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
include "../all.dfy"
include "base.dfy"
include "model.dfy"
include "soundness.dfy"

module validation.thm.strict_inf_strict {
  import opened typechecker
  import opened types
  import opened subtyping
  import opened base
  import opened model
  import opened soundness
  import opened def.core
  import opened def.engine
  import opened ext

  datatype StrictInfProof = StrictInfProof(
    reqty: RequestType,
    ets: EntityTypeStore,
    acts: ActionStore
  ) {

    predicate strictEnvironment() {
      reqty.context.isStrictType() &&
      reqty.principal.Some? &&
      reqty.resource.Some? &&
      forall k | k in ets.types.Keys ::  ets.types[k].isStrictType()
    }

    const S_TC := Typechecker(ets,acts,reqty, ValidationMode.Strict)

    lemma StrictRecord(e: Expr, r: seq<(Attr,Expr)>, effs: Effects)
      decreases r
      requires forall i | 0 <= i < |r| :: r[i] < e
      requires strictEnvironment()
      requires S_TC.inferRecord(e, r, effs).Ok?
      ensures S_TC.inferRecord(e, r, effs).value.isStrictType()
    {
      reveal S_TC.inferRecord();
      if r != [] {
        assert S_TC.infer(r[0].1,effs).value.0.isStrictType() by {StrictTypeInf(r[0].1, effs); }
        assert S_TC.inferRecord(e, r[1..], effs).value.isStrictType() by { StrictRecord(e, r[1..], effs); }
      }
    }

    lemma StrictSetElems(e: Expr, es: seq<Expr>, effs: Effects)
      decreases es
      requires forall i | 0 <= i < |es| :: es[i] < e
      requires strictEnvironment()
      requires S_TC.inferSet(e, es, effs).Ok?
      ensures es == [] ==> S_TC.inferSet(e, es, effs).value == Never
      ensures  es != [] ==> S_TC.inferSet(e, es, effs).value.isStrictType()
    {
      if es != []  {
        var (t,_) := S_TC.infer(es[0],effs).value;
        assert t.isStrictType() by { StrictTypeInf(es[0], effs); }
        var t1 := S_TC.inferSet(e,es[1..],effs).value;
        assert t1.isStrictType() || t1 == Never by { StrictSetElems(e, es[1..], effs); }
        var t2 := lubOpt(t,t1,ValidationMode.Strict).value;
        assert t2.isStrictType() by { StrictTypeLub(t, t1); }
      }
    }

    lemma StrictIf(g: Expr, t: Expr, e: Expr, effs: Effects)
      decreases If(g, t, e), 0
      requires strictEnvironment()
      requires S_TC.infer(If(g, t, e), effs).Ok?
      ensures S_TC.infer(If(g, t, e), effs).value.0.isStrictType()
    {
      var (bt,effs1) := S_TC.inferBoolType(g,effs).value;
      match bt {
        case True =>
          var (t1,effs2) := S_TC.infer(t,effs.union(effs1)).value;
          StrictTypeInf(t, effs.union(effs1));
        case False =>
          var (t2,effs2) := S_TC.infer(e,effs).value;
          StrictTypeInf(e, effs);
        case Bool =>
          var (t1,effs2) := S_TC.infer(t,effs.union(effs1)).value;
          var (t2,effs3) := S_TC.infer(e,effs).value;
          StrictTypeInf(t, effs.union(effs1));
          StrictTypeInf(e, effs);
          StrictTypeLub(t1, t2);
      }
    }

    lemma StrictGetAttr(e: Expr, l: Attr, effs:Effects)
      decreases GetAttr(e, l), 0
      requires strictEnvironment()
      requires S_TC.infer(GetAttr(e, l), effs).Ok?
      ensures S_TC.infer(GetAttr(e, l), effs).value.0.isStrictType()
    {
      assert S_TC.inferRecordEntityType(e,effs).Ok?;
      StrictTypeInf(e, effs);
    }

    lemma StrictHasAttr(e: Expr, l: Attr, effs: Effects)
      decreases HasAttr(e, l), 0
      requires strictEnvironment()
      requires S_TC.infer(HasAttr(e, l), effs).Ok?
      ensures S_TC.infer(HasAttr(e, l), effs).value.0.isStrictType()
    { }

    lemma StrictIn(e1: Expr, e2: Expr, effs: Effects)
      decreases BinaryApp(BinaryOp.In, e1, e2), 0
      requires strictEnvironment()
      requires S_TC.infer(BinaryApp(BinaryOp.In, e1, e2), effs).Ok?
      ensures S_TC.infer(BinaryApp(BinaryOp.In, e1, e2), effs).value.0.isStrictType()
    { }

    lemma StrictCall(name: base.Name, args: seq<Expr>, effs: Effects)
      decreases args
      requires strictEnvironment()
      requires S_TC.infer(Call(name, args), effs).Ok?
      ensures S_TC.infer(Call(name, args), effs).value.0.isStrictType()
    { }

    lemma StrictTypeInf(e: Expr, effs: Effects)
      decreases e, 1
      requires strictEnvironment()
      requires S_TC.infer(e, effs).Ok?
      ensures S_TC.infer(e, effs).value.0.isStrictType()
    {
      match e {
        case PrimitiveLit(p) =>
        case Var(x) =>
        case If(e',e1,e2) => StrictIf(e', e1, e2, effs);
        case And(e1,e2) =>
        case Or(e1,e2) =>
        case UnaryApp(Not,e') =>
        case UnaryApp(Neg,e') =>
        case UnaryApp(MulBy(i),e') =>
        case UnaryApp(Like(p),e') =>
        case BinaryApp(Eq,e1,e2) =>
        case BinaryApp(Less,e1,e2) =>
        case BinaryApp(LessEq,e1,e2) =>
        case BinaryApp(Add,e1,e2) =>
        case BinaryApp(Sub,e1,e2) =>
        case BinaryApp(In,e1,e2) => StrictIn(e1, e2, effs);
        case BinaryApp(ContainsAny,e1,e2) =>
        case BinaryApp(ContainsAll,e1,e2) =>
        case BinaryApp(Contains,e1,e2) =>
        case Record(es) => StrictRecord(e, es, effs);
        case Set(es) => StrictSetElems(e, es, effs);
        case GetAttr(e',l) => StrictGetAttr(e', l, effs);
        case HasAttr(e',l) => StrictHasAttr(e', l, effs);
        case Call(name,es) => StrictCall(name, es, effs);
      }
    }
  }
}
