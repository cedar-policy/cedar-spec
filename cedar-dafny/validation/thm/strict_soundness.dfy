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

// This module contains the proof of soundness for strict typechecking.
module validation.thm.strict_soundness {
  import opened typechecker
  import opened types
  import opened subtyping
  import opened base
  import opened model
  import opened soundness
  import opened def.core
  import opened def.engine
  import opened ext

  datatype StrictProof = StrictProof(
    reqty: RequestType,
    ets: EntityTypeStore,
    acts: ActionStore
  ) {

    const P_TC := Typechecker(ets,acts,reqty, ValidationMode.Permissive)
    const S_TC := Typechecker(ets,acts,reqty, ValidationMode.Strict)

    lemma StrictCallArgs(e: Expr, args: seq<Expr>, tys: seq<Type>, effs: Effects)
      decreases args, tys
      requires |args| == |tys|
      requires forall i | 0 <= i < |args| :: args[i] < e
      requires S_TC.inferCallArgs(e, args, tys, effs).Ok?
      ensures P_TC.inferCallArgs(e, args, tys, effs).Ok?
    {
      if args != [] {
        var (t,effs') := S_TC.infer(args[0], effs).value;
        assert P_TC.infer(args[0], effs) == Ok((t, effs')) by { StrictTypecheckingIsStrict(args[0], effs); }

        assert subty(t, tys[0], ValidationMode.Strict);
        assert subty(t, tys[0], ValidationMode.Permissive) by { StrictSubtyIsStrict(t, tys[0]); }

        assert S_TC.inferCallArgs(e, args[1..], tys[1..], effs).Ok?;
        assert P_TC.inferCallArgs(e, args[1..], tys[1..], effs).Ok? by { StrictCallArgs(e, args[1..], tys[1..], effs); }
      }
    }

    lemma StrictCall(name: base.Name, args: seq<Expr>, effs: Effects)
      decreases args
      requires S_TC.infer(Call(name, args), effs).Ok?
      ensures P_TC.infer(Call(name, args), effs) == S_TC.infer(Call(name, args), effs)
    {
      var ty := extFunTypes[name];
      assert S_TC.inferCallArgs(Call(name, args), args, ty.args, effs).Ok?;
      assert P_TC.inferCallArgs(Call(name, args), args, ty.args, effs).Ok? by { StrictCallArgs(Call(name, args), args, ty.args, effs); }
    }

    lemma StrictSetElems(e: Expr, es: seq<Expr>, effs: Effects)
      decreases es
      requires forall i | 0 <= i < |es| :: es[i] < e
      requires S_TC.inferSet(e, es, effs).Ok?
      ensures P_TC.inferSet(e, es, effs) == S_TC.inferSet(e, es, effs)
    {
      if es != [] {
        var (t, effs') := S_TC.infer(es[0], effs).value;
        assert P_TC.infer(es[0], effs) == Ok((t, effs')) by { StrictTypecheckingIsStrict(es[0], effs); }

        var t1 := S_TC.inferSet(e, es[1..], effs).value;
        assert P_TC.inferSet(e, es[1..], effs) == Ok(t1) by { StrictSetElems(e, es[1..], effs); }

        var lub := lub(t, t1, ValidationMode.Strict);
        assert lubOpt(t, t1, ValidationMode.Permissive) == Ok(lub) by { StrictLubIsStrict(t, t1); }
      }
    }

    lemma StrictNot(e: Expr, effs: Effects)
      decreases UnaryApp(Not, e), 0
      requires S_TC.infer(UnaryApp(Not, e), effs).Ok?
      ensures P_TC.infer(UnaryApp(Not, e), effs) == S_TC.infer(UnaryApp(Not, e), effs)
    {
      assert P_TC.inferBoolType(e, effs) == S_TC.inferBoolType(e, effs) by {
        StrictTypecheckingIsStrict(e, effs);
      }
    }

    lemma StrictArith1(o: UnaryOp, e: Expr, effs: Effects)
      decreases UnaryApp(o, e), 0
      requires o.Neg? || o.MulBy?
      requires S_TC.infer(UnaryApp(o, e), effs).Ok?
      ensures P_TC.infer(UnaryApp(o, e), effs) == S_TC.infer(UnaryApp(o, e), effs)
    {
      var (min1, max1) := S_TC.ensureIntType(e, effs).value;
      assert P_TC.ensureIntType(e, effs) == S_TC.ensureIntType(e, effs) by { StrictTypecheckingIsStrict(e, effs); }
    }

    lemma StrictLike(p: Pattern, e: Expr, effs: Effects)
      decreases UnaryApp(Like(p), e), 0
      requires S_TC.infer(UnaryApp(Like(p), e), effs).Ok?
      ensures P_TC.infer(UnaryApp(Like(p), e), effs) == S_TC.infer(UnaryApp(Like(p), e), effs)
    {
      assert P_TC.ensureStringType(e, effs).Ok? by {
        assert S_TC.ensureStringType(e, effs).Ok?;
        StrictTypecheckingIsStrict(e, effs);
      }
    }

    lemma StrictArith2Ineq(o: BinaryOp, e1: Expr, e2: Expr, effs: Effects)
      decreases BinaryApp(o, e1, e2), 0
      requires o.Add? || o.Sub? || o.Less? || o.LessEq?
      requires S_TC.infer(BinaryApp(o, e1, e2), effs).Ok?
      ensures P_TC.infer(BinaryApp(o, e1, e2), effs) == S_TC.infer(BinaryApp(o, e1, e2), effs)
    {
      var (min1, max1) := S_TC.ensureIntType(e1, effs).value;
      assert P_TC.ensureIntType(e1, effs) == S_TC.ensureIntType(e1, effs) by { StrictTypecheckingIsStrict(e1, effs); }
      var (min2, max2) := S_TC.ensureIntType(e2, effs).value;
      assert P_TC.ensureIntType(e2, effs) == S_TC.ensureIntType(e2, effs) by { StrictTypecheckingIsStrict(e2, effs); }
    }

    lemma StrictLubRecordTypeSeq(rts: seq<RecordType>)
      requires lubRecordTypeSeq(rts, ValidationMode.Strict).Ok?
      ensures lubRecordTypeSeq(rts, ValidationMode.Permissive) == lubRecordTypeSeq(rts, ValidationMode.Strict)
    {
      assert rts != [];
      if |rts| != 1 {
        var tailLub := lubRecordTypeSeq(rts[1..], ValidationMode.Strict).value;
        assert lubRecordTypeSeq(rts[1..], ValidationMode.Permissive) == Ok(tailLub) by { StrictLubRecordTypeSeq(rts[1..]); }

        assert lubRecordType(rts[0], tailLub, ValidationMode.Strict) == lubRecordType(rts[0], tailLub, ValidationMode.Permissive) by {
          StrictLubIsStrict(Type.Record(rts[0]), Type.Record(tailLub));
        }
      }
    }

    lemma StrictGetLubRecordType(lub: EntityLUB)
      requires ets.getLubRecordType(lub, ValidationMode.Strict).Ok?
      ensures ets.getLubRecordType(lub, ValidationMode.Permissive) == ets.getLubRecordType(lub, ValidationMode.Strict)
    {
      if lub.AnyEntity? || exists et <- lub.tys :: isAction(et) {
        assert ets.getLubRecordType(lub, ValidationMode.Permissive).Ok?;
      } else {
        assert forall et <- lub.tys :: et in ets.types;
        def.util.EntityTypeLeqIsTotalOrder();
        var lubSeq := def.util.SetToSortedSeq(lub.tys,def.util.EntityTypeLeq);
        var s := seq (|lubSeq|, i requires 0 <= i < |lubSeq| => ets.types[lubSeq[i]]);
        assert lubRecordTypeSeq(s, ValidationMode.Strict) == lubRecordTypeSeq(s, ValidationMode.Permissive) by {
          assert ets.getLubRecordType(lub, ValidationMode.Strict).Ok?;
          StrictLubRecordTypeSeq(s);
        }
      }
    }

    lemma StrictHasAttr(e: Expr, l: Attr, effs: Effects)
      decreases HasAttr(e, l), 0
      requires S_TC.infer(HasAttr(e, l), effs).Ok?
      ensures P_TC.infer(HasAttr(e, l), effs) == S_TC.infer(HasAttr(e, l), effs)
    {
      var ret := S_TC.inferRecordEntityType(e, effs).value;
      assert P_TC.inferRecordEntityType(e, effs) == Ok(ret) by { StrictTypecheckingIsStrict(e, effs); }

      match ret {
        case Record(rt) =>
        case Entity(lub) =>
          if ets.isAttrPossible(lub,l) {
            var rt := ets.getLubRecordType(lub, ValidationMode.Strict).value;
            assert ets.getLubRecordType(lub, ValidationMode.Permissive) == Ok(rt) by { StrictGetLubRecordType(lub); }
          }
      }
    }

    lemma StrictGetAttr(e: Expr, l: Attr, effs:Effects)
      decreases GetAttr(e, l), 0
      requires S_TC.infer(GetAttr(e, l), effs).Ok?
      ensures P_TC.infer(GetAttr(e, l), effs) == S_TC.infer(GetAttr(e, l), effs)
    {
      var ret := S_TC.inferRecordEntityType(e, effs).value;
      assert P_TC.inferRecordEntityType(e, effs) == Ok(ret) by { StrictTypecheckingIsStrict(e, effs); }

      match ret {
        case Record(rt) =>
        case Entity(lub) => {
          var rt := ets.getLubRecordType(lub, ValidationMode.Strict).value;
          assert ets.getLubRecordType(lub, ValidationMode.Permissive) == Ok(rt) by { StrictGetLubRecordType(lub); }
        }
      }
    }

    lemma StrictIf(g: Expr, t: Expr, e: Expr, effs: Effects)
      decreases If(g, t, e), 0
      requires S_TC.infer(If(g, t, e), effs).Ok?
      ensures P_TC.infer(If(g, t, e), effs) == S_TC.infer(If(g, t, e), effs)
    {
      var (gt, ge) := S_TC.inferBoolType(g, effs).value;
      assert P_TC.inferBoolType(g, effs) == Ok((gt, ge)) by { StrictTypecheckingIsStrict(g, effs); }

      match gt {
        case True => {
          var (tt, te) := S_TC.infer(t, effs.union(ge)).value;
          assert P_TC.infer(t, effs.union(ge)) == Ok((tt, te)) by { StrictTypecheckingIsStrict(t, effs.union(ge)); }
        }
        case False => {
          var (et, ee) := S_TC.infer(e, effs).value;
          assert P_TC.infer(e, effs) == Ok((et, ee)) by { StrictTypecheckingIsStrict(e, effs); }
        }
        case Bool => {
          var (tt, te) := S_TC.infer(t, effs.union(ge)).value;
          assert P_TC.infer(t, effs.union(ge)) == Ok((tt, te)) by { StrictTypecheckingIsStrict(t, effs.union(ge)); }

          var (et, ee) := S_TC.infer(e, effs).value;
          assert P_TC.infer(e, effs) == Ok((et, ee)) by { StrictTypecheckingIsStrict(e, effs); }

          var lub := lub(tt, et, ValidationMode.Strict);
          assert lubOpt(tt, et, ValidationMode.Permissive) == Ok(lub) by { StrictLubIsStrict(tt, et); }
        }
      }
    }

    lemma StrictEq(e1: Expr, e2: Expr, effs: Effects)
      decreases BinaryApp(BinaryOp.Eq, e1, e2), 0
      requires S_TC.infer(BinaryApp(BinaryOp.Eq, e1, e2), effs).Ok?
      ensures P_TC.infer(BinaryApp(BinaryOp.Eq, e1, e2), effs) == S_TC.infer(BinaryApp(BinaryOp.Eq, e1, e2), effs)
    {
      var (t1, effs1) := S_TC.infer(e1, effs).value;
      assert  P_TC.infer(e1, effs) == Ok((t1, effs1)) by { StrictTypecheckingIsStrict(e1, effs); }

      var (t2, effs2) := S_TC.infer(e2, effs).value;
      assert P_TC.infer(e2, effs) == Ok((t2, effs2)) by { StrictTypecheckingIsStrict(e2, effs); }
    }

    lemma StrictContainsAnyAll(o: BinaryOp, e1: Expr, e2: Expr, effs: Effects)
      decreases BinaryApp(o, e1, e2), 0
      requires o.ContainsAny? || o.ContainsAll?
      requires S_TC.infer(BinaryApp(o, e1, e2), effs).Ok?
      ensures P_TC.infer(BinaryApp(o, e1, e2), effs) == S_TC.infer(BinaryApp(o, e1, e2), effs)
    {
      var t1 := S_TC.inferSetType(e1, effs).value;
      assert  P_TC.inferSetType(e1, effs) == Ok(t1) by { StrictTypecheckingIsStrict(e1, effs); }

      var t2 := S_TC.inferSetType(e2, effs).value;
      assert P_TC.inferSetType(e2, effs) == Ok(t2) by { StrictTypecheckingIsStrict(e2, effs); }
    }

    lemma StrictContains(e1: Expr, e2: Expr, effs: Effects)
      decreases BinaryApp(BinaryOp.Contains, e1, e2), 0
      requires S_TC.infer(BinaryApp(BinaryOp.Contains, e1, e2), effs).Ok?
      ensures P_TC.infer(BinaryApp(BinaryOp.Contains, e1, e2), effs) == S_TC.infer(BinaryApp(BinaryOp.Contains, e1, e2), effs)
    {
      var t1 := S_TC.inferSetType(e1, effs).value;
      assert  P_TC.inferSetType(e1, effs) == Ok(t1) by { StrictTypecheckingIsStrict(e1, effs); }

      var (t2, effs2) := S_TC.infer(e2, effs).value;
      assert P_TC.infer(e2, effs) == Ok((t2, effs2)) by { StrictTypecheckingIsStrict(e2, effs); }
    }

    lemma StrictIn(e1: Expr, e2: Expr, effs: Effects)
      decreases BinaryApp(BinaryOp.In, e1, e2), 0
      requires S_TC.infer(BinaryApp(BinaryOp.In, e1, e2), effs).Ok?
      ensures P_TC.infer(BinaryApp(BinaryOp.In, e1, e2), effs) == S_TC.infer(BinaryApp(BinaryOp.In, e1, e2), effs)
    {
      assert S_TC.ensureEntityType(e1,effs).Ok?;
      assert P_TC.ensureEntityType(e1,effs).Ok? by { StrictTypecheckingIsStrict(e1, effs); }

      assert S_TC.ensureEntitySetType(e2,effs).Ok?;
      assert P_TC.ensureEntitySetType(e2,effs).Ok? by { StrictTypecheckingIsStrict(e2, effs); }

      var (t2, effs') := S_TC.infer(e2,effs).value;
      assert P_TC.infer(e2, effs) == Ok((t2, effs')) by { StrictTypecheckingIsStrict(e2, effs); }
    }

    lemma StrictAnd(e1: Expr, e2: Expr, effs: Effects)
      decreases And(e1, e2), 0
      requires S_TC.infer(And(e1, e2), effs).Ok?
      ensures P_TC.infer(And(e1, e2), effs) == S_TC.infer(And(e1, e2), effs)
    {
      var (bt1,effs1) := S_TC.inferBoolType(e1,effs).value;
      assert P_TC.inferBoolType(e1,effs) == Ok((bt1, effs1)) by { StrictTypecheckingIsStrict(e1, effs); }

      match bt1 {
        case True => {
          var (bt2,effs2) := S_TC.inferBoolType(e2,effs.union(effs1)).value;
          assert P_TC.inferBoolType(e2,effs.union(effs1)) == Ok((bt2, effs2)) by { StrictTypecheckingIsStrict(e2, effs.union(effs1)); }
        }
        case False =>
        case Bool => {
          var (bt2,effs2) := S_TC.inferBoolType(e2,effs.union(effs1)).value;
          assert P_TC.inferBoolType(e2,effs.union(effs1)) == Ok((bt2, effs2)) by { StrictTypecheckingIsStrict(e2, effs.union(effs1)); }
        }
      }
    }

    lemma StrictOr(e1: Expr, e2: Expr, effs: Effects)
      decreases Or(e1, e2), 0
      requires S_TC.infer(Or(e1, e2), effs).Ok?
      ensures P_TC.infer(Or(e1, e2), effs) == S_TC.infer(Or(e1, e2), effs)
    {
      var (bt1,effs1) := S_TC.inferBoolType(e1,effs).value;
      assert P_TC.inferBoolType(e1,effs) == Ok((bt1, effs1)) by { StrictTypecheckingIsStrict(e1, effs); }

      match bt1 {
        case True =>
        case False => {
          var (bt2,effs2) := S_TC.inferBoolType(e2,effs).value;
          assert P_TC.inferBoolType(e2,effs) == Ok((bt2, effs2)) by { StrictTypecheckingIsStrict(e2, effs); }
        }
        case Bool => {
          var (bt2,effs2) := S_TC.inferBoolType(e2,effs).value;
          assert P_TC.inferBoolType(e2,effs) == Ok((bt2, effs2)) by { StrictTypecheckingIsStrict(e2, effs); }
        }
      }
    }

    lemma StrictRecord(e: Expr, r: seq<(Attr,Expr)>, effs: Effects)
      decreases r
      requires forall i | 0 <= i < |r| :: r[i] < e
      requires S_TC.inferRecord(e, r, effs).Ok?
      ensures P_TC.inferRecord(e, r, effs) == S_TC.inferRecord(e, r, effs)
    {
      reveal S_TC.inferRecord();
      if r != [] {
        var (t,effs') := S_TC.infer(r[0].1,effs).value;
        assert P_TC.infer(r[0].1, effs) == Ok((t, effs')) by {StrictTypecheckingIsStrict(r[0].1, effs); }

        var m := S_TC.inferRecord(e, r[1..], effs).value;
        assert P_TC.inferRecord(e, r[1..], effs) == Ok(m) by { StrictRecord(e, r[1..], effs); }
      }
    }

    lemma StrictTypecheckingIsStrict(e: Expr, effs: Effects)
      decreases e, 1
      requires S_TC.infer(e, effs).Ok?
      ensures P_TC.infer(e, effs) == S_TC.infer(e, effs)
    {
      match e {
        case PrimitiveLit(p) =>
        case Var(x) =>
        case If(e',e1,e2) => StrictIf(e', e1, e2, effs);
        case And(e1,e2) => StrictAnd(e1, e2, effs);
        case Or(e1,e2) => StrictOr(e1, e2, effs);
        case UnaryApp(Not,e') => StrictNot(e', effs);
        case UnaryApp(Neg,e') => StrictArith1(Neg, e', effs);
        case UnaryApp(MulBy(i),e') => StrictArith1(MulBy(i), e', effs);
        case UnaryApp(Like(p),e') => StrictLike(p, e', effs);
        case BinaryApp(Eq,e1,e2) => StrictEq(e1, e2, effs);
        case BinaryApp(Less,e1,e2) => StrictArith2Ineq(Less, e1, e2, effs);
        case BinaryApp(LessEq,e1,e2) => StrictArith2Ineq(LessEq, e1, e2, effs);
        case BinaryApp(Add,e1,e2) => StrictArith2Ineq(Add, e1, e2, effs);
        case BinaryApp(Sub,e1,e2) => StrictArith2Ineq(Sub, e1, e2, effs);
        case BinaryApp(In,e1,e2) => StrictIn(e1, e2, effs);
        case BinaryApp(ContainsAny,e1,e2) => StrictContainsAnyAll(ContainsAny, e1, e2, effs);
        case BinaryApp(ContainsAll,e1,e2) => StrictContainsAnyAll(ContainsAll, e1, e2, effs);
        case BinaryApp(Contains,e1,e2) => StrictContains(e1, e2, effs);
        case Record(es) => StrictRecord(e, es, effs);
        case Set(es) => StrictSetElems(e, es, effs);
        case GetAttr(e',l) => StrictGetAttr(e', l, effs);
        case HasAttr(e',l) => StrictHasAttr(e', l, effs);
        case Call(name,es) => StrictCall(name, es, effs);
      }
    }
  }
}
