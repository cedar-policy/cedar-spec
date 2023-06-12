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

include "../def/all.dfy"
include "types.dfy"
include "ext.dfy"
include "subtyping.dfy"

// This module contains the specification of Cedar's permissive typechecker,
// which is the core of the Cedar validator (see validator.dfy).
module validation.typechecker {
  import def
  import opened def.core
  import opened types
  import opened ext
  import opened subtyping

  // --------- Entity Type Store --------- //

  // The Entity Type Store records the attributes associated with each
  // entity type, and the hierarchy between entity types. Note that we do not
  // enforce that the possibleDescendantOf relationship is transitive.
  datatype EntityTypeStore = EntityTypeStore(
    types: map<EntityType,RecordType>,
    descendants: map<EntityType,set<EntityType>>
  ) {
    // Check if an entity of type et1 can be a descendent of an entity of type et2
    predicate possibleDescendantOf(et1: EntityType, et2: EntityType)
    {
      if et1 == et2 then true
      else if et2 in descendants
      then et1 in descendants[et2]
      else false
    }

    predicate possibleDescendantOfSet(et: EntityType, ets: set<EntityType>)
    {
      exists et1 <- ets :: possibleDescendantOf(et,et1)
    }

    // Get the RecordType common to all entity types in the LUB
    function getLubRecordType(lub: EntityLUB): Result<RecordType>
    {
      if lub.AnyEntity? || exists et <- lub.tys :: isAction(et)
      then Ok(RecordType(map[], true))
      else
        if forall et <- lub.tys :: et in types
        then
          def.util.EntityTypeLeqIsTotalOrder();
          var lubSeq := def.util.SetToSortedSeq(lub.tys,def.util.EntityTypeLeq);
          lubRecordTypeSeq(seq (|lubSeq|, i requires 0 <= i < |lubSeq| => types[lubSeq[i]]))
        else Err(UnknownEntities(set et <- lub.tys | et !in types :: et))
    }

    // Check if an Attr is allowed by any entity type in the LUB
    predicate isAttrPossible(lub: EntityLUB, k: Attr)
    {
      lub.AnyEntity? || exists e <- lub.tys :: e in types && (types[e].is_open || k in types[e].attrs)
    }
  }

  // --------- Action Store --------- //

  // The Action Store records the hierarchy between actions. This is different
  // from the Entity Type Store because it stores the literal EUIDs of actions in
  // the hierarchy, rather than their types. Like the Entity Type Store, we do
  // not enforce that the descendantOf relationship is transitive.
  datatype ActionStore = ActionStore(
    descendants: map<EntityUID,set<EntityUID>>
  ) {
    // Check if an euid1 is a descendent of euid2.
    predicate descendantOf(euid1: EntityUID, euid2: EntityUID)
    {
      if euid1 == euid2 then true
      else if euid2 in descendants
      then euid1 in descendants[euid2]
      else false
    }

    predicate descendantOfSet(euid: EntityUID, euids: set<EntityUID>)
    {
      exists euid1 <- euids :: descendantOf(euid, euid1)
    }
  }

  // --------- Request Type --------- //

  // Types for the four variables bound in the request,
  // generated from the schema using a cross-product.
  // If a field is None, then it is an "Unspecified" entity.
  datatype RequestType = RequestType (
    principal: Option<EntityType>,
    action: EntityUID,
    resource: Option<EntityType>,
    context: RecordType
  )

  // --------- Effects --------- //

  // Effects are used for occurrence typing. An (e,a) pair represents that
  // attribute a is known to exist for expression e.
  datatype Effects = Effects(effs: set<(Expr,Attr)>)
  {
    function union(other: Effects): Effects {
      Effects(this.effs + other.effs)
    }

    function intersect(other: Effects): Effects {
      Effects(this.effs * other.effs)
    }

    predicate contains(e: Expr, a: Attr) {
      (e,a) in this.effs
    }

    static function empty(): Effects {
      Effects({})
    }

    static function singleton(e: Expr, a: Attr): Effects {
      Effects({(e,a)})
    }
  }

  // --------- Typechecker --------- //

  // A Typechecker is a standard bidirectional typechecker for Cedar.
  // It expects an EntityTypeStore, ActionStore, and RequestType as input.
  // The two main functions (typecheck and infer) are at the bottom of the
  // datatype, with helpers at the top.
  datatype Typechecker = Typechecker(ets: EntityTypeStore, acts: ActionStore, reqty: RequestType){

    function ensureSubty(t1: Type, t2: Type): (res: Result<()>)
    {
      if subty(t1,t2) then Ok(())
      else Err(SubtyErr(t1,t2))
    }

    function ensureStringType(e: Expr, effs: Effects): Result<()>
      decreases e , 2
    {
      var (t,_) :- infer(e,effs);
      match t {
        case String => Ok(())
        case _ => Err(UnexpectedType(t))
      }
    }

    function ensureIntType(e: Expr, effs: Effects): Result<()>
      decreases e , 2
    {
      var (t,_) :- infer(e,effs);
      match t {
        case Int => Ok(())
        case _ => Err(UnexpectedType(t))
      }
    }

    function ensureEntityType(e: Expr, effs: Effects): Result<()>
      decreases e , 2
    {
      var (t,_) :- infer(e,effs);
      match t {
        case Entity(_) => Ok(())
        case _ => Err(UnexpectedType(t))
      }
    }

    function ensureEntitySetType(e: Expr, effs: Effects): Result<()>
      decreases e , 2
    {
      var (t,_) :- infer(e,effs);
      match t {
        case Entity(_) => Ok(())
        case Set(Entity(_)) => Ok(())
        case Set(Never) => Ok(()) // empty set is also valid
        case _ => Err(UnexpectedType(t))
      }
    }

    function inferPrim(p: Primitive): Result<Type> {
      match p {
        case Bool(true) => Ok(Type.Bool(True))
        case Bool(false) => Ok(Type.Bool(False))
        case Int(_) => Ok(Type.Int)
        case String(_) => Ok(Type.String)
        case EntityUID(u) =>
          if u.ty in ets.types || isAction(u.ty)
          then Ok(Type.Entity(EntityLUB({u.ty})))
          else Err(UnknownEntities({u.ty}))
      }
    }

    function inferVar(x: Var): Result<Type> {
      match x {
        case Principal =>
          if reqty.principal.None?
          then Ok(Type.Entity(AnyEntity))
          else Ok(Type.Entity(EntityLUB({reqty.principal.value})))
        case Context => Ok(Type.Record(reqty.context))
        case Action => Ok(Type.Entity(EntityLUB({reqty.action.ty})))
        case Resource =>
          if reqty.resource.None?
          then Ok(Type.Entity(AnyEntity))
          else Ok(Type.Entity(EntityLUB({reqty.resource.value})))
      }
    }

    function inferBoolType(e: Expr, effs: Effects): Result<(BoolType,Effects)>
      decreases e , 2
    {
      var (t,effs1) :- infer(e,effs);
      match t {
        case Bool(bt) => Ok((bt,effs1))
        case _ => Err(UnexpectedType(t))
      }
    }

    function inferSetType(e: Expr, effs: Effects): Result<Type>
      decreases e , 2
    {
      var (t,_) :- infer(e,effs);
      match t {
        case Set(t1) => Ok(t1)
        case _ => Err(UnexpectedType(t))
      }
    }

    function inferRecordEntityType(e: Expr, effs: Effects): Result<RecordEntityType>
      decreases e , 2
    {
      var (t,_) :- infer(e,effs);
      match t {
        case Record(rt) => Ok(RecordEntityType.Record(rt))
        case Entity(lub) => Ok(RecordEntityType.Entity(lub))
        case _ => Err(UnexpectedType(t))
      }
    }

    // If e1 is known to be true, then return the union of the effects of e1 and e2.
    // If e1 is known to be false, then return the effects of e3.
    // Otherwise, return the union of the effects of e1 and e2 (the "true" case)
    // intersected with the effects of e3 (the "false" case).
    function inferIf(e1: Expr, e2: Expr, e3: Expr, effs: Effects): Result<(Type,Effects)>
      decreases If(e1,e2,e3) , 0
    {
      var (bt,effs1) :- inferBoolType(e1,effs);
      match bt {
        case True =>
          var (t,effs2) :- infer(e2,effs.union(effs1));
          Ok((t,effs1.union(effs2)))
        case False => infer(e3,effs)
        case Bool =>
          var (t1,effs2) :- infer(e2,effs.union(effs1));
          var (t2,effs3) :- infer(e3,effs);
          var t :- lubOpt(t1,t2);
          Ok((t,effs1.union(effs2).intersect(effs3)))
      }
    }

    // If e1 or e2 is known to be false, then return the empty set of effects.
    // Otherwise, return the union of the effects of e1 and e2.
    // The returned effects will hold iff the runtime value of And(e1,e2) is true.
    function inferAnd(e1: Expr, e2: Expr, effs: Effects): Result<(Type,Effects)>
      decreases And(e1,e2) , 0
    {
      var (bt1,effs1) :- inferBoolType(e1,effs);
      match bt1 {
        case False => wrap(Ok(Type.Bool(False)))
        case _ =>
          var (bt2,effs2) :- inferBoolType(e2,effs.union(effs1));
          match bt2 {
            case False => wrap(Ok(Type.Bool(False)))
            case True => Ok((Type.Bool(bt1),effs1.union(effs2)))
            case _ => Ok((Type.Bool(AnyBool),effs1.union(effs2)))
          }
      }
    }

    // If e1 is known to be true, then return the effects of e1.
    // If e1 is known to be false, then return the effects of e2.
    // If e1 is unknown and e2 is known to be true, then return the effects of e2.
    // If e1 is unknown and e2 is known to be false, then return the effects of e1.
    // Otherwise, return the intersection of the effects of e1 and e2.
    // The returned effects will hold iff the runtime value of Or(e1,e2) is true.
    function inferOr(e1: Expr, e2: Expr, effs: Effects): Result<(Type,Effects)>
      decreases Or(e1,e2) , 0
    {
      var (bt1,effs1) :- inferBoolType(e1,effs);
      match bt1 {
        case True => wrap(Ok(Type.Bool(True)))
        case False =>
          var (bt2,effs2) :- inferBoolType(e2,effs);
          Ok((Type.Bool(bt2),effs2))
        case _ =>
          var (bt2,effs2) :- inferBoolType(e2,effs);
          match bt2 {
            case True => wrap(Ok(Type.Bool(True)))
            case False => Ok((Type.Bool(bt1),effs1))
            case _ => Ok((Type.Bool(AnyBool),effs1.intersect(effs2)))
          }
      }
    }

    function inferNot(e: Expr, effs: Effects): Result<Type>
      decreases UnaryApp(Not,e) , 0
    {
      var (bt,_) :- inferBoolType(e,effs);
      Ok(Type.Bool(bt.not()))
    }

    function isUnspecifiedVar(e: Expr): bool {
      match e {
        case Var(Principal) => reqty.principal.None?
        case Var(Resource) => reqty.resource.None?
        case _ => false
      }
    }

    function inferEq(e1: Expr, e2: Expr, effs: Effects): (res: Result<Type>)
      decreases BinaryApp(BinaryOp.Eq,e1,e2) , 0
    {
      var (t1,_) :- infer(e1,effs);
      var (t2,_) :- infer(e2,effs);
      if t1.Entity? && t2.Entity? && t1.lub.disjoint(t2.lub)
      then Ok(Type.Bool(False))
      else if isUnspecifiedVar(e1) && t2.Entity? && t2.lub.specified()
        then Ok(Type.Bool(False))
        else match (e1,e2) {
            case (PrimitiveLit(EntityUID(u1)),PrimitiveLit(EntityUID(u2))) =>
              if u1 == u2 then Ok(Type.Bool(True)) else Ok(Type.Bool(False))
            case _ => Ok(Type.Bool(AnyBool))
          }
    }

    function inferIneq(ghost op: BinaryOp, e1: Expr, e2: Expr, effs: Effects): Result<Type>
      requires op == Less || op == LessEq
      decreases BinaryApp(op,e1,e2) , 0
    {
      var _ :- ensureIntType(e1,effs);
      var _ :- ensureIntType(e2,effs);
      Ok(Type.Bool(AnyBool))
    }

    function tryGetEUID(e: Expr): Option<EntityUID> {
      match e {
        case PrimitiveLit(EntityUID(euid)) => Option.Some(euid)
        case _ => Option.None
      }
    }

    function tryGetEUIDs(e: Expr): Option<set<EntityUID>> {
      match e {
        case Set(es) =>
          if forall e1 <- es :: tryGetEUID(e1).Some?
          then Option.Some(set e1 <- es :: tryGetEUID(e1).value)
          else Option.None
        case _ => Option.None
      }
    }

    function getPrincipalOrResource(v: Var): Option<EntityType>
      requires v == Var.Principal || v == Var.Resource
    {
      match v {
        case Principal => reqty.principal
        case Resource => reqty.resource
      }
    }

    function inferIn(ghost parent: Expr, e1: Expr, e2: Expr, effs: Effects): Result<Type>
      requires e1 < parent
      requires e2 < parent
      decreases parent , 0 , e2
    {
      // check that LHS is an entity
      var _ :- ensureEntityType(e1,effs);
      // check that RHS is an entity or a set of entities
      var _ :- ensureEntitySetType(e2,effs);
      var (t2, _) := infer(e2,effs).value;
      if isUnspecifiedVar(e1) && match t2 {
           case Entity(lub) => lub.specified()
           case Set(Entity(lub)) => lub.specified()
           // `Set(Never)` is the type of the empty set. It would also be safe to
           // return true in this case, but false matches the Rust implementation.
           case Set(Never) => false
         }
      then Ok(Type.Bool(False))
      else match (e1,e2) {
          // We substitute `Var::Action` for its literal EntityUID prior to
          // validation, so the real logic for handling Actions is in the entity
          // literal case below. We return an imprecise default answer here.
          case (Var(Action),_) => Ok(Type.Bool(AnyBool))
          // LHS is Principal or Resource
          case (Var(v),PrimitiveLit(EntityUID(u))) =>
            var et := getPrincipalOrResource(v);
            // Note: When `et.None?`, typing `e1 in e2` as false would be
            // unsound without some additional hypothesis that the literal(s) in
            // e2 are not unspecified entities. We expect that case to be
            // handled by the `isUnspecifiedVar` code above, so we don't handle
            // it again here.
            var b := et.None? || ets.possibleDescendantOf(et.value,u.ty);
            if b then Ok(Type.Bool(AnyBool)) else Ok(Type.Bool(False))
          case (Var(v),Set(_)) =>
            var et := getPrincipalOrResource(v);
            match tryGetEUIDs(e2) {
              case Some(euids) =>
                var es := set euid <- euids :: euid.ty;
                var b := et.None? || ets.possibleDescendantOfSet(et.value,es);
                if b then Ok(Type.Bool(AnyBool)) else Ok(Type.Bool(False))
              case None => Ok(Type.Bool(AnyBool))
            }
          // LHS is entity literal (or action, per above)
          case (PrimitiveLit(EntityUID(u1)),PrimitiveLit(EntityUID(u2))) =>
            // If the entity literal is an action, then use acts.descendantOf.
            // Otherwise, use ets.possibleDescendantOf.
            if isAction(u1.ty)
            then
              if acts.descendantOf(u1,u2) then Ok(Type.Bool(AnyBool)) else Ok(Type.Bool(False))
            else
              var b := ets.possibleDescendantOf(u1.ty,u2.ty);
              if b then Ok(Type.Bool(AnyBool)) else Ok(Type.Bool(False))
          case (PrimitiveLit(EntityUID(u)),Set(_)) =>
            match tryGetEUIDs(e2) {
              case Some(euids) =>
                // If the entity literal is an action, then use acts.descendantOfSet.
                // Otherwise, use ets.possibleDescendantOfSet.
                if isAction(u.ty)
                then
                  if acts.descendantOfSet(u,euids) then Ok(Type.Bool(AnyBool)) else Ok(Type.Bool(False))
                else
                  var es := set euid <- euids :: euid.ty;
                  var b := ets.possibleDescendantOfSet(u.ty,es);
                  if b then Ok(Type.Bool(AnyBool)) else Ok(Type.Bool(False))
              case None => Ok(Type.Bool(AnyBool))
            }
          // otherwise, the result is unknown so return Bool
          case _ => Ok(Type.Bool(AnyBool))
        }
    }

    function inferContainsAnyAll(b: BinaryOp, e1: Expr, e2: Expr, effs: Effects): Result<Type>
      requires b == ContainsAny || b == ContainsAll
      decreases BinaryApp(b,e1,e2), 0
    {
      var s1 :- inferSetType(e1,effs);
      var s2 :- inferSetType(e2,effs);
      Ok(Type.Bool(AnyBool))
    }

    function inferContains(e1: Expr, e2: Expr, effs: Effects): Result<Type>
      decreases BinaryApp(Contains,e1,e2) , 0
    {
      var s :- inferSetType(e1,effs);
      var t :- infer(e2,effs);
      Ok(Type.Bool(AnyBool))
    }

    function {:opaque true} inferRecord(ghost e: Expr, r: seq<(Attr,Expr)>, effs: Effects): (res: Result<RecordType>)
      requires forall i | 0 <= i < |r| :: r[i] < e
      decreases e , 0 , r
    {
      if r == [] then
        Ok(RecordType(map[], false))
      else
        var k := r[0].0;
        var (t,_) :- infer(r[0].1,effs);
        assert r[0] < e;
        var m :- inferRecord(e,r[1..],effs);
        Ok(RecordType(if k in m.attrs.Keys then m.attrs else m.attrs[k := AttrType(t,true)], false))
    }

    function inferHasAttrHelper(e: Expr, k: Attr, rt: RecordType, effs: Effects, knownToExist: bool): Result<(Type,Effects)>
    {
      if k in rt.attrs
      then
        if rt.attrs[k].isRequired && knownToExist then wrap(Ok(Type.Bool(True)))
        else if effs.contains(e,k)
        then wrap(Ok(Type.Bool(True)))
        else Ok((Type.Bool(AnyBool),Effects.singleton(e,k)))
      else if rt.is_open
      then wrap(Ok(Type.Bool(AnyBool)))
      else wrap(Ok(Type.Bool(False)))
    }

    function inferHasAttr(e: Expr, k: Attr, effs: Effects): Result<(Type,Effects)>
      decreases HasAttr(e,k) , 0
    {
      var ret :- inferRecordEntityType(e,effs);
      match ret {
        case Record(rt) => inferHasAttrHelper(e,k,rt,effs,true)
        case Entity(lub) =>
          if !ets.isAttrPossible(lub,k) then wrap(Ok(Type.Bool(False)))
          else
            (var rt :- ets.getLubRecordType(lub);
             inferHasAttrHelper(e,k,rt,effs,false))

      }
    }

    function inferLike(p: Pattern, e: Expr, effs: Effects): Result<Type>
      decreases UnaryApp(Like(p),e) , 0
    {
      var _ :- ensureStringType(e,effs);
      Ok(Type.Bool(AnyBool))
    }

    function inferArith1(ghost op: UnaryOp, e: Expr, effs: Effects): Result<Type>
      requires op.Neg? || op.MulBy?
      decreases UnaryApp(op,e) , 0
    {
      var _ :- ensureIntType(e,effs);
      Ok(Type.Int)
    }

    function inferArith2(ghost op: BinaryOp, e1: Expr, e2: Expr, effs: Effects): Result<Type>
      requires op == Add || op == Sub
      decreases BinaryApp(op,e1,e2) , 0
    {
      var _ :- ensureIntType(e1,effs);
      var _ :- ensureIntType(e2,effs);
      Ok(Type.Int)
    }

    function inferGetAttr(e: Expr, k: Attr, effs: Effects): Result<Type>
      decreases GetAttr(e,k) , 0
    {
      var ret :- inferRecordEntityType(e,effs);
      match ret {
        case Record(rt) =>
          if k in rt.attrs && (rt.attrs[k].isRequired || effs.contains(e,k))
          then Ok(rt.attrs[k].ty)
          else Err(AttrNotFound(Type.Record(rt),k))
        case Entity(lub) =>
          var rt :- ets.getLubRecordType(lub);
          if k in rt.attrs && (rt.attrs[k].isRequired || effs.contains(e,k))
          then Ok(rt.attrs[k].ty)
          else Err(AttrNotFound(Type.Entity(lub),k))
      }
    }

    function inferSet(ghost e: Expr, r: seq<Expr>, effs: Effects): (res: Result<Type>)
      requires forall i | 0 <= i < |r| :: r[i] < e
      decreases e , 0 , r
    {
      if r == [] then
        Ok(Type.Never)
      else
        var (t,_) :- infer(r[0],effs);
        var t1 :- inferSet(e,r[1..],effs);
        var t2 :- lubOpt(t,t1);
        Ok(t2)
    }

    // Utility to convert `Ok(T)` to `Ok(T,Effects.empty())`
    function wrap(t: Result<Type>): Result<(Type,Effects)> {
      t.Map(t0 => (t0,Effects.empty()))
    }

    function inferCallArgs(ghost e: Expr, args: seq<Expr>, tys: seq<Type>, effs: Effects): Result<()>
      requires |args| == |tys|
      requires forall i | 0 <= i < |args| :: args[i] < e
      decreases e , 0 , args
    {
      if args == [] then
        Ok(())
      else
        var (t,_) :- infer(args[0],effs);
        var _ :- ensureSubty(t,tys[0]);
        inferCallArgs(e,args[1..],tys[1..],effs)
    }

    function inferCall(ghost e: Expr, name: base.Name, args: seq<Expr>, effs: Effects): Result<Type>
      requires forall i | 0 <= i < |args| :: args[i] < e
      decreases e , 0
    {
      if name in extFunTypes.Keys
      then
        var ty := extFunTypes[name];
        // check that the function uses the expected number of arguments
        var _ :- if |args| == |ty.args| then Ok(()) else Err(ExtensionErr(Call(name,args)));
        // check that all args are a subtype of the expected type
        var _ :- inferCallArgs(e,args,ty.args,effs);
        // run the optional argument check
        var _ :- match ty.check {
          case Some(f) => f(args)
          case None => Ok(())
        };
        // if we reach this point, then type checking was successful
        Ok(ty.ret)
      else Err(ExtensionErr(Call(name,args)))
    }

    // Inference is fully syntax directed: we simply crawl over the term and
    // read off the type. This is only possible without annotation because
    // Cedar has no binders. If in the future Cedar gets functions, they will
    // have to have type signatures for this bidirectional system to continue
    // working.
    //
    // `effs` tracks the attributes that are known to exist for prior (enclosing)
    // expressions. The returned effects are new effects introduced by
    // typing the current expression.
    function infer(e: Expr, effs: Effects): Result<(Type,Effects)>
      decreases e , 1
    {
      match e {
        case PrimitiveLit(p) => wrap(inferPrim(p))
        case Var(x) => wrap(inferVar(x))
        case If(e1,e2,e3) => inferIf(e1,e2,e3,effs)
        case And(e1,e2) => inferAnd(e1,e2,effs)
        case Or(e1,e2) => inferOr(e1,e2,effs)
        case UnaryApp(Not,e1) => wrap(inferNot(e1,effs))
        case UnaryApp(Neg,e1) => wrap(inferArith1(Neg,e1,effs))
        case UnaryApp(MulBy(i),e1) => wrap(inferArith1(MulBy(i),e1,effs))
        case UnaryApp(Like(p),e1) => wrap(inferLike(p,e1,effs))
        case BinaryApp(Eq,e1,e2) => wrap(inferEq(e1,e2,effs))
        case BinaryApp(Less,e1,e2) => wrap(inferIneq(Less,e1,e2,effs))
        case BinaryApp(LessEq,e1,e2) => wrap(inferIneq(LessEq,e1,e2,effs))
        case BinaryApp(In,e1,e2) => wrap(inferIn(e,e1,e2,effs))
        case BinaryApp(Add,e1,e2) => wrap(inferArith2(Add,e1,e2,effs))
        case BinaryApp(Sub,e1,e2) => wrap(inferArith2(Sub,e1,e2,effs))
        case BinaryApp(ContainsAny,e1,e2) => wrap(inferContainsAnyAll(ContainsAny,e1,e2,effs))
        case BinaryApp(ContainsAll,e1,e2) => wrap(inferContainsAnyAll(ContainsAll,e1,e2,effs))
        case BinaryApp(Contains,e1,e2) => wrap(inferContains(e1,e2,effs))
        case Record(r) => var rt :- inferRecord(Expr.Record(r),r,effs); wrap(Ok(Type.Record(rt)))
        case Set(es) => var st :- inferSet(e,es,effs); wrap(Ok(Type.Set(st)))
        case HasAttr(e1,k) => inferHasAttr(e1,k,effs)
        case GetAttr(e1,k) => wrap(inferGetAttr(e1,k,effs))
        case Call(name,args) => wrap(inferCall(e,name,args,effs))
      }
    }

    // The standard "turn-around" rule of a bidirectional type system forms the
    // top-level interface for the expression-level part of the validator.
    function typecheck(e: Expr, t: Type): Result<Type> {
      // call infer with an empty effect set
      var (t1,_) :- infer(e,Effects.empty());
      // check that the result of inference is a subtype of t
      var _ :- ensureSubty(t1,t);
      Ok(t1)
    }

  }

}
