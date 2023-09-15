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

  predicate subtyAttrType(a1: AttrType, a2: AttrType) {
    subty(a1.ty, a2.ty) && (a2.isRequired ==> a1.isRequired)
  }

  predicate subtyRecordType(rt1: RecordType, rt2: RecordType)
    decreases Type.Record(rt1) , Type.Record(rt2) , 0
  {
    rt2.Keys <= rt1.Keys &&
    (forall k | k in rt2.Keys ::
       subtyAttrType(rt1[k], rt2[k]))
  }

  predicate subtyEntity(lub1: EntityLUB, lub2: EntityLUB) {
    lub1.subset(lub2)
  }

  predicate subty(t1: Type, t2: Type) {
    match (t1,t2) {
      case (Never,_) => true
      case (String,String) => true
      case (Int,Int) => true
      case (Bool(b1),Bool(b2)) => subtyBool(b1,b2)
      case (Set(t11),Set(t21)) => subty(t11,t21)
      case (Record(rt1),Record(rt2)) => subtyRecordType(rt1,rt2)
      case (Entity(lub1),Entity(lub2)) => subtyEntity(lub1,lub2)
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

  function lubEntity(lub1: EntityLUB, lub2: EntityLUB): EntityLUB {
    lub1.union(lub2)
  }

  function lubAttrType(a1: AttrType, a2: AttrType): AttrType
    requires lubOpt(a1.ty, a2.ty).Ok?
  {
    AttrType(lubOpt(a1.ty, a2.ty).value, a1.isRequired && a2.isRequired)
  }

  // This function produces a valid lub for any two maps, including ones that
  // are inconsistent. For example: the upper bound of { foo: Int } and
  // { foo: String } is the empty map type {}. This decision was made for the
  // sake of consistency with the Rust production implementation.
  function lubRecordType(rt1: RecordType, rt2: RecordType): RecordType
    decreases Type.Record(rt1) , Type.Record(rt2) , 0
  {
    map k | k in rt1.Keys && k in rt2.Keys && lubOpt(rt1[k].ty, rt2[k].ty).Ok? ::
         lubAttrType(rt1[k], rt2[k])
  }

  function lubRecordTypeSeq(rts: seq<RecordType>): Result<RecordType>
  {
    if rts == [] then Err(EmptyLUB)
    else if |rts| == 1 then Ok(rts[0])
    else
      var res :- lubRecordTypeSeq(rts[1..]);
      Ok(lubRecordType(rts[0],res))
  }

  function lubOpt(t1: Type, t2: Type): Result<Type>
    decreases t1, t2 , 1
  {
    match (t1,t2) {
      case (Never,_) => Ok(t2)
      case (_,Never) => Ok(t1)
      case (String,String) => Ok(Type.String)
      case (Int,Int) => Ok(Type.Int)
      case (Bool(b1),Bool(b2)) => Ok(Type.Bool(lubBool(b1,b2)))
      case (Entity(lub1),Entity(lub2)) => Ok(Type.Entity(lubEntity(lub1,lub2)))
      case (Set(t11),Set(t12)) =>
        var t :- lubOpt(t11,t12);
        Ok(Type.Set(t))
      case(Record(rt1),Record(rt2)) =>
        Ok(Type.Record(lubRecordType(rt1,rt2)))
      case (Extension(e1),Extension(e2)) =>
        if e1 == e2 then Ok(Extension(e1))
        else Err(LubErr(t1,t2))
      case _ => Err(LubErr(t1,t2))
    }
  }

  ghost predicate LubDefined(t1: Type,t2: Type) {
    match lubOpt(t1,t2) {
      case Ok(_) => true
      case _ => false
    }
  }

  function lub(t1: Type, t2: Type):  Type
    requires LubDefined(t1,t2)
  {
    match lubOpt(t1,t2) {
      case Ok(t) => t
    }
  }

  lemma SubtyRefl(t: Type)
    ensures subty(t,t)
  {}

  lemma SubtyRecordTypeRefl(rt: RecordType)
    ensures subtyRecordType(rt, rt)
  {
    forall k | k in rt.Keys ensures subtyAttrType(rt[k], rt[k]) {
      SubtyRefl(rt[k].ty);
    }
  }

  lemma SubtyRecordTypeTrans(rt1: RecordType, rt2: RecordType, rt3: RecordType)
    requires subtyRecordType(rt1,rt2)
    requires subtyRecordType(rt2,rt3)
    ensures subtyRecordType(rt1,rt3)
    decreases Type.Record(rt1) , Type.Record(rt2) , Type.Record(rt3) , 0
  {
    assert rt3.Keys <= rt1.Keys;
    forall k | k in rt3.Keys
      ensures subty(rt1[k].ty, rt3[k].ty)
      ensures rt3[k].isRequired ==> rt1[k].isRequired
    {
      assert subty(rt1[k].ty, rt2[k].ty);
      assert subty(rt2[k].ty, rt3[k].ty);
      SubtyTrans(rt1[k].ty, rt2[k].ty, rt3[k].ty);
    }
  }

  lemma SubtyTrans(t1: Type, t2: Type, t3: Type)
    requires subty(t1,t2)
    requires subty(t2,t3)
    ensures subty(t1,t3)
  {
    match (t1,t2,t3) {
      case (Record(rt1),Record(rt2),Record(rt3)) => SubtyRecordTypeTrans(rt1,rt2,rt3);
      case _ =>
    }
  }

  lemma LubIsUB(t1: Type, t2: Type, t: Type)
    requires lubOpt(t1,t2) == Ok(t)
    ensures subty(t1,t)
    ensures subty(t2,t)
  {
    match (t1,t2,t) {
      case (Never,_,_) => assert t2 == t; SubtyRefl(t);
      case (_,Never,_) => assert t1 == t; SubtyRefl(t);
      case (Int,Int,Int) =>
      case (String,String,String) =>
      case(Bool(b1),Bool(b2),Bool(bt)) =>
      case (Entity(e1),Entity(e2),Entity(e)) =>
      case (Set(t1'),Set(t2'),Set(t')) => LubIsUB(t1',t2',t');
      case(Record(rt1'),Record(rt2'),Record(rt')) =>
        assert rt'.Keys <= rt1'.Keys;
        assert rt'.Keys <= rt2'.Keys;
        assert subty(Type.Record(rt1'),Type.Record(rt')) by {
          forall k | k in rt'.Keys
            ensures subtyAttrType(rt1'[k],rt'[k])
          {
            assert rt'[k] == lubAttrType(rt1'[k],rt2'[k]);
            assert lubOpt(rt1'[k].ty,rt2'[k].ty) == Ok(rt'[k].ty);
            LubIsUB(rt1'[k].ty,rt2'[k].ty,rt'[k].ty);
          }
        }
        assert subty(Type.Record(rt2'),Type.Record(rt')) by {
          forall k | k in rt'.Keys
            ensures subtyAttrType(rt2'[k],rt'[k])
          {
            assert rt'[k] == lubAttrType(rt1'[k],rt2'[k]);
            assert lubOpt(rt1'[k].ty,rt2'[k].ty) == Ok(rt'[k].ty);
            LubIsUB(rt1'[k].ty,rt2'[k].ty,rt'[k].ty);
          }
        }
      case (Extension(n1),Extension(n2),Extension(n)) =>
    }
  }
}
