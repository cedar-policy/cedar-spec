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

  predicate subtyRecordType(rt1: RecordType, rt2: RecordType)
    decreases Type.Record(rt1) , Type.Record(rt2) , 0
  {
    rt2.Keys <= rt1.Keys &&
    (forall k | k in rt2.Keys ::
       subty(rt1[k].ty, rt2[k].ty) &&
       (rt2[k].isRequired ==> rt1[k].isRequired))
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

  // This function produces a valid lub for any two maps, including ones that
  // are inconsistent. For example: the upper bound of { foo: Int } and
  // { foo: String } is the empty map type {}. This decision was made for the
  // sake of consistency with the Rust production implementation.
  function lubRecordType(rt1: RecordType, rt2: RecordType): Result<RecordType>
    decreases Type.Record(rt1) , Type.Record(rt2) , 0
  {
    Ok(map k | k in rt1.Keys && k in rt2.Keys && lubOpt(rt1[k].ty, rt2[k].ty).Ok? ::
         AttrType(lubOpt(rt1[k].ty, rt2[k].ty).value, rt1[k].isRequired && rt2[k].isRequired))
  }

  function lubRecordTypeSeq(rts: seq<RecordType>): Result<RecordType>
  {
    if rts == [] then Err(EmptyLUB)
    else if |rts| == 1 then Ok(rts[0])
    else
      var res :- lubRecordTypeSeq(rts[1..]);
      lubRecordType(rts[0],res)
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
        var rt :- lubRecordType(rt1,rt2);
        Ok(Type.Record(rt))
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
}
