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

include "types.dfy"

module validation.subtyping {
  import opened types

  predicate subtyBool(b1: BoolType, b2: BoolType) {
    match (b1,b2) {
      case (_,AnyBool) => true
      case (True,True) => true
      case (False,False) => true
      case _ => false
    }
  }

  predicate subtyAttrType(a1: AttrType, a2: AttrType, m: ValidationMode) {
    subty(a1.ty, a2.ty, m) && (a2.isRequired ==> a1.isRequired)
  }

  predicate subtyRecordType(rt1: RecordType, rt2: RecordType, m: ValidationMode)
    decreases Type.Record(rt1) , Type.Record(rt2) , 0
  {
    (rt1.isOpen() ==> rt2.isOpen()) &&
    // width subtyping
    rt2.attrs.Keys <= rt1.attrs.Keys &&
    // depth subtyping
    (forall k | k in rt2.attrs.Keys ::
       subtyAttrType(rt1.attrs[k], rt2.attrs[k], m)) &&
    // disable width subtyping if `rt2` is closed or we are in strict mode.
    ((!rt2.isOpen() || m.isStrict()) ==> rt1.attrs.Keys == rt2.attrs.Keys)
  }

  predicate subtyEntity(lub1: EntityLUB, lub2: EntityLUB, m:ValidationMode) {
    if m.isStrict()
    then lub1 == lub2
    else lub1.subset(lub2)
  }

  predicate subty(t1: Type, t2: Type, m: ValidationMode)
    decreases t1, t2
  {
    match (t1,t2) {
      case (Never,_) => true
      case (String,String) => true
      case (Int(min1,max1),Int(min2,max2)) => min1 >= min2 && max1 <= max2
      case (Bool(b1),Bool(b2)) => subtyBool(b1,b2)
      case (Set(t11),Set(t21)) => subty(t11,t21,m)
      case (Record(rt1),Record(rt2)) => subtyRecordType(rt1,rt2,m)
      case (Entity(lub1),Entity(lub2)) => subtyEntity(lub1,lub2,m)
      case (Extension(e1),Extension(e2)) => e1 == e2
      case _ => false
    }
  }

  function lubBool(b1: BoolType, b2: BoolType): BoolType {
    match (b1,b2) {
      case (True,True) => True
      case (False,False) => False
      case _ => AnyBool
    }
  }

  function lubEntity(lub1: EntityLUB, lub2: EntityLUB, m: ValidationMode): Result<EntityLUB> {
    if m.isStrict() && lub1 != lub2
    then Err(LubErr(Type.Entity(lub1), Type.Entity(lub2)))
    else Ok(lub1.union(lub2))
  }

  function lubAttrType(a1: AttrType, a2: AttrType, m: ValidationMode): AttrType
    requires lubOpt(a1.ty, a2.ty, m).Ok?
  {
    AttrType(lubOpt(a1.ty, a2.ty, m).value, a1.isRequired && a2.isRequired)
  }

  // In permissive mode, this function produces a valid lub for any two maps, including ones that
  // are inconsistent. For example: the upper bound of { foo: Int } and
  // { foo: String } is the empty map type {}. This decision was made for the
  // sake of consistency with the Rust production implementation.
  // In strict mode, a lub does not exist for the case described above. A lub
  // will also not exist if any field exists in one record type without existing
  // in the other.
  function lubRecordType(rt1: RecordType, rt2: RecordType, m: ValidationMode): Result<RecordType>
    decreases Type.Record(rt1) , Type.Record(rt2) , 0
  {
    var attrs :=
      map k | k in rt1.attrs.Keys && k in rt2.attrs.Keys && lubOpt(rt1.attrs[k].ty, rt2.attrs[k].ty, m).Ok? ::
        lubAttrType(rt1.attrs[k], rt2.attrs[k], m);
    var lubDropsAttr := attrs.Keys != (rt1.attrs.Keys + rt2.attrs.Keys);
    if m.isStrict() && lubDropsAttr
    then Err(LubErr(Type.Record(rt1), Type.Record(rt2)))
    else
      var openTag := if rt1.isOpen() || rt2.isOpen() || lubDropsAttr then OpenAttributes else ClosedAttributes;
      Ok(RecordType(attrs, openTag))
  }

  function lubRecordTypeSeq(rts: seq<RecordType>, m: ValidationMode): Result<RecordType>
  {
    if rts == [] then Err(EmptyLUB)
    else if |rts| == 1 then Ok(rts[0])
    else
      var res :- lubRecordTypeSeq(rts[1..],m);
      lubRecordType(rts[0],res,m)
  }

  function i64Min(x: i64, y: i64): i64 {
    if x < y then x else y
  }
  function i64Max(x: i64, y: i64): i64 {
    if x > y then x else y
  }

  function lubOpt(t1: Type, t2: Type, m: ValidationMode): Result<Type>
    decreases t1, t2 , 1
  {
    match (t1,t2) {
      case (Never,_) => Ok(t2)
      case (_,Never) => Ok(t1)
      case (String,String) => Ok(Type.String)
      case (Int(min1,max1),Int(min2,max2)) => Ok(Type.Int(i64Min(min1,min2),i64Max(max1,max2)))
      case (Bool(b1),Bool(b2)) => Ok(Type.Bool(lubBool(b1,b2)))
      case (Entity(lub1),Entity(lub2)) =>
        var elub :- lubEntity(lub1,lub2, m);
        Ok(Type.Entity(elub))
      case (Set(t11),Set(t12)) =>
        var t :- lubOpt(t11,t12, m);
        Ok(Type.Set(t))
      case(Record(rt1),Record(rt2)) =>
        var rtlub :- lubRecordType(rt1,rt2,m);
        Ok(Type.Record(rtlub))
      case (Extension(e1),Extension(e2)) =>
        if e1 == e2 then Ok(Extension(e1))
        else Err(LubErr(t1,t2))
      case _ => Err(LubErr(t1,t2))
    }
  }

  ghost predicate LubDefined(t1: Type,t2: Type, m: ValidationMode) {
    match lubOpt(t1,t2, m) {
      case Ok(_) => true
      case _ => false
    }
  }

  function lub(t1: Type, t2: Type, m: ValidationMode):  Type
    requires LubDefined(t1,t2,m)
  {
    match lubOpt(t1,t2,m) {
      case Ok(t) => t
    }
  }

  lemma SubtyRefl(t: Type)
    ensures forall m :: subty(t,t, m)
  {
    match t {
      case Record(rt) => SubtyRecordTypeRefl(rt);
      case _ =>
    }
  }

  lemma SubtyRecordTypeRefl(rt: RecordType)
    ensures forall m :: subtyRecordType(rt, rt, m)
  {
    forall m, k | k in rt.attrs.Keys ensures subtyAttrType(rt.attrs[k], rt.attrs[k], m) {
      SubtyRefl(rt.attrs[k].ty);
    }
  }

  lemma SubtyRecordTypeTrans(rt1: RecordType, rt2: RecordType, rt3: RecordType, m: ValidationMode)
    requires subtyRecordType(rt1,rt2,m)
    requires subtyRecordType(rt2,rt3,m)
    ensures subtyRecordType(rt1,rt3,m)
    decreases Type.Record(rt1) , Type.Record(rt2) , Type.Record(rt3) , 0
  {
    assert rt3.attrs.Keys <= rt1.attrs.Keys;
    forall k | k in rt3.attrs.Keys
      ensures subty(rt1.attrs[k].ty, rt3.attrs[k].ty, m)
      ensures rt3.attrs[k].isRequired ==> rt1.attrs[k].isRequired
    {
      assert subty(rt1.attrs[k].ty, rt2.attrs[k].ty, m);
      assert subty(rt2.attrs[k].ty, rt3.attrs[k].ty, m);
      SubtyTrans(rt1.attrs[k].ty, rt2.attrs[k].ty, rt3.attrs[k].ty, m);
    }
  }

  lemma SubtyTrans(t1: Type, t2: Type, t3: Type, m: ValidationMode)
    requires subty(t1,t2,m)
    requires subty(t2,t3,m)
    ensures subty(t1,t3,m)
    decreases t1, t2, t3
  {
    match (t1,t2,t3) {
      case (Record(rt1),Record(rt2),Record(rt3)) => SubtyRecordTypeTrans(rt1,rt2,rt3,m);
      case _ =>
    }
  }

  lemma LubIsUB(t1: Type, t2: Type, t: Type, m: ValidationMode)
    requires lubOpt(t1,t2,m) == Ok(t)
    ensures subty(t1,t,m)
    ensures subty(t2,t,m)
  {
    match (t1,t2,t) {
      case (Never,_,_) => assert t2 == t; SubtyRefl(t);
      case (_,Never,_) => assert t1 == t; SubtyRefl(t);
      case (Int(min1,max1),Int(min2,max2),Int(mint,maxt)) =>
      case (String,String,String) =>
      case(Bool(b1),Bool(b2),Bool(bt)) =>
      case (Entity(e1),Entity(e2),Entity(e)) =>
      case (Set(t1'),Set(t2'),Set(t')) => LubIsUB(t1',t2',t',m);
      case(Record(rt1'),Record(rt2'),Record(rt')) =>
        assert rt'.attrs.Keys <= rt1'.attrs.Keys;
        assert rt'.attrs.Keys <= rt2'.attrs.Keys;
        assert subty(Type.Record(rt1'),Type.Record(rt'),m) by {
          forall k | k in rt'.attrs.Keys
            ensures subtyAttrType(rt1'.attrs[k],rt'.attrs[k],m)
          {
            assert rt'.attrs[k] == lubAttrType(rt1'.attrs[k],rt2'.attrs[k],m);
            assert lubOpt(rt1'.attrs[k].ty,rt2'.attrs[k].ty,m) == Ok(rt'.attrs[k].ty);
            LubIsUB(rt1'.attrs[k].ty,rt2'.attrs[k].ty,rt'.attrs[k].ty,m);
          }
        }
        assert subty(Type.Record(rt2'),Type.Record(rt'),m) by {
          forall k | k in rt'.attrs.Keys
            ensures subtyAttrType(rt2'.attrs[k],rt'.attrs[k],m)
          {
            assert rt'.attrs[k] == lubAttrType(rt1'.attrs[k],rt2'.attrs[k],m);
            assert lubOpt(rt1'.attrs[k].ty,rt2'.attrs[k].ty,m) == Ok(rt'.attrs[k].ty);
            LubIsUB(rt1'.attrs[k].ty,rt2'.attrs[k].ty,rt'.attrs[k].ty,m);
          }
        }
      case (Extension(n1),Extension(n2),Extension(n)) =>
    }
  }

  lemma LubUndefUbUndef(t1 : Type, t2 : Type, t : Type, m: ValidationMode)
    requires !LubDefined(t1, t2, m)
    ensures !subty(t1, t, m) || !subty(t2, t, m)
  {
    match t {
      case Never =>
      case Int(_, _) =>
      case String =>
      case Bool(b) =>
      case Entity(e) =>
      case Set(e) => {
        if t1.Set? && t2.Set? {
          LubUndefUbUndef(t1.ty, t2.ty, e, m);
        }
      }
      case Record(rt) => {
        match (t1, t2) {
          case (Record(rt1), Record(rt2)) => {
            if m.isStrict() {
              assert lubRecordType(rt1, rt2, ValidationMode.Strict).Err?;

              if exists k | k in rt1.attrs.Keys && k in rt2.attrs.Keys :: !LubDefined(rt1.attrs[k].ty, rt2.attrs[k].ty, m) {
                var k :| k in rt1.attrs.Keys && k in rt2.attrs.Keys && !LubDefined(rt1.attrs[k].ty, rt2.attrs[k].ty, m);
                if k in rt.attrs.Keys {
                  assert (exists k' | k' in rt.attrs.Keys && k' in rt1.attrs.Keys :: !subtyAttrType(rt1.attrs[k'], rt.attrs[k'], m)) ||
                         (exists k' | k' in rt.attrs.Keys && k' in rt2.attrs.Keys :: !subtyAttrType(rt2.attrs[k'], rt.attrs[k'], m));
                }
              }
            } else {
              assert lubRecordType(rt1, rt2, ValidationMode.Permissive).Ok?;
            }
          }
          case _ =>
        }
      }
      case Extension(e) =>
    }
  }

  lemma StrictSubtyIsStrict(t1: Type, t2: Type)
    requires subty(t1, t2, ValidationMode.Strict)
    ensures subty(t1, t2, ValidationMode.Permissive)
  {
    match (t1,t2) {
      case (Record(rt1),Record(rt2)) =>  {
        if(rt2.attrs.Keys <= rt1.attrs.Keys) {
          if ! (forall k | k in rt2.attrs.Keys :: subtyAttrType(rt1.attrs[k], rt2.attrs[k], ValidationMode.Permissive)) {
            assert exists k | k in rt2.attrs.Keys :: !subtyAttrType(rt1.attrs[k], rt2.attrs[k], ValidationMode.Permissive);
            assert exists k | k in rt2.attrs.Keys :: !subtyAttrType(rt1.attrs[k], rt2.attrs[k], ValidationMode.Strict);
          }
        }
      }
      case _ =>
    }
  }

  lemma StrictLubIsStrict(t1: Type, t2: Type)
    requires LubDefined(t1, t2, ValidationMode.Strict)
    ensures lubOpt(t1, t2, ValidationMode.Permissive) == lubOpt(t1, t2, ValidationMode.Strict)
  {
    match (t1,t2) {
      case (Never,_) =>
      case (_,Never) =>
      case (Int(_, _),Int(_, _)) =>
      case (String,String) =>
      case (Bool(b1),Bool(b2)) =>
      case (Entity(e1),Entity(e2)) =>
      case (Set(t1'),Set(t2')) =>
      case (Record(rt1),Record(rt2)) => {
        assert lubRecordType(rt1, rt2, ValidationMode.Strict).Ok?;
        assert lubRecordType(rt1, rt2, ValidationMode.Permissive).Ok?;

        var strict_attrs :=
          map k | k in rt1.attrs.Keys && k in rt2.attrs.Keys && lubOpt(rt1.attrs[k].ty, rt2.attrs[k].ty, ValidationMode.Strict).Ok? ::
            lubAttrType(rt1.attrs[k], rt2.attrs[k], ValidationMode.Strict);
        assert strict_attrs == lubRecordType(rt1, rt2, ValidationMode.Strict).value.attrs;

        var permissive_attrs :=
          map k | k in rt1.attrs.Keys && k in rt2.attrs.Keys && lubOpt(rt1.attrs[k].ty, rt2.attrs[k].ty, ValidationMode.Permissive).Ok? ::
            lubAttrType(rt1.attrs[k], rt2.attrs[k], ValidationMode.Permissive);
        assert permissive_attrs == lubRecordType(rt1, rt2, ValidationMode.Permissive).value.attrs;

        assert permissive_attrs == strict_attrs;
      }
      case (Extension(n1),Extension(n2)) =>
    }
  }

  // Proof that the LUB of two strict types is also strict. Additionally proves
  // that the LUB is still strict if one of `t1` or `t2` is `Never` (not a
  // strict type) which is required for proving that strict typechecking infers
  // a strict type for sets.
  lemma StrictTypeLub(t1: Type, t2: Type)
    requires t1.isStrictType() || t1 == Never
    requires t2.isStrictType() || t2 == Never
    requires t1 != Never || t2 != Never
    requires LubDefined(t1, t2, ValidationMode.Strict)
    ensures lub(t1, t2, ValidationMode.Strict).isStrictType()
  {
    match (t1,t2) {
      case (Never,_) =>
      case (_,Never) =>
      case (Int(_, _),Int(_, _)) =>
      case (String,String) =>
      case (Bool(b1),Bool(b2)) =>
      case (Entity(e1),Entity(e2)) => assert e1 == e1.union(e2);
      case (Set(t1'),Set(t2')) => StrictTypeLub(t1', t2');
      case (Record(rt1),Record(rt2)) => {
        var strict_attrs :=
          map k | k in rt1.attrs.Keys && k in rt2.attrs.Keys && lubOpt(rt1.attrs[k].ty, rt2.attrs[k].ty, ValidationMode.Strict).Ok? ::
            lubAttrType(rt1.attrs[k], rt2.attrs[k], ValidationMode.Strict);
        assert strict_attrs == lubRecordType(rt1, rt2, ValidationMode.Strict).value.attrs;

        forall k | k in strict_attrs.Keys
          ensures strict_attrs[k].ty.isStrictType()
        {
          StrictTypeLub(rt1.attrs[k].ty, rt2.attrs[k].ty);
        }
      }
      case (Extension(n1),Extension(n2)) =>
    }
  }
}
