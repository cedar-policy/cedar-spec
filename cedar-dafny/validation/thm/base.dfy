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

// This module contains the basic definitions used to state type soundness.
module validation.thm.base {
  import opened def.base
  import opened def.core
  import opened def.engine
  import opened types
  import opened subtyping
  import opened typechecker

  function Evaluate(e: Expr, r: Request, s: EntityStore): base.Result<Value>
  {
    Evaluator(r, s).interpret(e)
  }

  const unspecifiedPrincipalEuid := EntityUID.EntityUID(EntityType.UNSPECIFIED, "principal")
  const unspecifiedResourceEuid := EntityUID.EntityUID(EntityType.UNSPECIFIED, "resource")

  ghost predicate InstanceOfRequestType(r: Request, reqty: RequestType) {
    match reqty.principal {
      case None => r.principal == unspecifiedPrincipalEuid
      case Some(pt) => InstanceOfEntityType(r.principal, pt)
    } &&
    r.action == reqty.action &&
    match reqty.resource {
      case None => r.resource == unspecifiedResourceEuid
      case Some(rt) => InstanceOfEntityType(r.resource, rt)
    } &&
    InstanceOfRecordType(r.context, reqty.context)
  }

  ghost predicate InstanceOfEntityType(e: EntityUID, ety: EntityType) {
    ety == e.ty
  }

  // Note that this is stronger than the alternative
  //   `InstanceOfType(Value.Record(r), Type.Record(rt))`
  // because it enforces that the record type `rt` exactly describes the
  // fields in `r`.
  ghost predicate InstanceOfRecordType(r: Record, rt: RecordType) {
    // all attributes are declared and well typed
    (forall k | k in r :: k in rt && InstanceOfType(r[k], rt[k].ty)) &&
    // required attributes are present
    (forall k | k in rt && rt[k].isRequired :: k in r)
  }

  ghost predicate InstanceOfEntityTypeStore(s: EntityStore, ets: EntityTypeStore)
  {
    forall e | e in s.entities.Keys ::
      var ety := e.ty;
      var edata := s.entities[e];
      // The EntityStore cannot contain unspecified entities. In particular,
      // they cannot have ancestors, so they cannot be `in` other entities.
      ety != EntityType.UNSPECIFIED &&
      ety in ets.types &&
      InstanceOfRecordType(edata.attrs, ets.types[ety]) &&
      forall p | p in edata.ancestors ::
        p.ty in ets.descendants && ety in ets.descendants[p.ty]
  }

  ghost predicate InstanceOfActionStore(s: EntityStore, acts: ActionStore)
  {
    forall e | e in s.entities.Keys && isAction(e.ty) ::
      var edata := s.entities[e];
      forall p | p in edata.ancestors ::
        p in acts.descendants && e in acts.descendants[p]
  }

  function typeOfPrim(p: Primitive): Type {
    match p {
      case Bool(true) => Type.Bool(True)
      case Bool(false) => Type.Bool(False)
      case Int(i) => Type.Int(i,i)
      case String(_) => Type.String
      case EntityUID(u) => Type.Entity(EntityLUB({u.ty}))
    }
  }

  ghost predicate InstanceOfBoolType(b: bool, bt: BoolType) {
    match (b,bt) {
      case (true,True) => true
      case (false,False) => true
      case (_,AnyBool) => true
      case _ => false
    }
  }

  // Letting this accept `int` rather than `i64` lets us use it in `model.dfy`
  // on results of unbounded Dafny arithmetic operations that we haven't yet
  // proved to be in range of an `i64`.
  ghost predicate InstanceOfIntType(i: int, ty: Type)
    requires ty.Int?
  {
    ty.min <= i <= ty.max
  }

  const intTopType := Type.Int(types.i64_MIN, types.i64_MAX)

  ghost predicate InstanceOfEntityLUB(e: EntityUID, ty: EntityLUB) {
    match ty {
      case AnyEntity => true
      case EntityLUB(lub) => exists et | et in lub :: InstanceOfEntityType(e, et)
    }
  }

  ghost predicate InstanceOfType(v: Value, ty: Type)
    decreases ty
  {
    match (v,ty) {
      case (Primitive(Bool(b)),Bool(bt)) => InstanceOfBoolType(b,bt)
      case (Primitive(Int(i)),Int(min,max)) => min <= i <= max
      case (Primitive(String(_)),String) => true
      case (Primitive(EntityUID(e)),Entity(lub)) => InstanceOfEntityLUB(e,lub)
      case (Set(s),Set(ty1)) =>
        forall v1 | v1 in s :: InstanceOfType(v1,ty1)
      case (Record(r),Record(rt)) =>
        // if an attribute is present, then it has the expected type
        (forall k | k in rt && k in r :: InstanceOfType(r[k],rt[k].ty)) &&
        // required attributes are present
        (forall k | k in rt && rt[k].isRequired :: k in r)
      case (Extension(Decimal(_)),_) => ty == Type.Extension(Name.fromStr("decimal"))
      case (Extension(IPAddr(_)),_) => ty == Type.Extension(Name.fromStr("ipaddr"))
      case _ => false
    }
  }
}
