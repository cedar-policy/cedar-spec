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
include "typechecker.dfy"

// This module defines the strict typechecking algorithm, which is exposed
// to users through `Validator.validate`.
module validation.strict {
  import opened def
  import opened def.core
  import opened types
  import opened typechecker
  import opened ext

  datatype StrictTypeError =
    // Error returned by the permissive typechecker
    TypeError(TypeError) |
    // Error specific to strict typechecking
    TypesMustMatch |
    EmptySetForbidden |
    NonLitExtConstructor |
    NonSingletonLub

  type Result<T> = std.Result<T,StrictTypeError>

  datatype StrictTypechecker = StrictTypechecker(ets: EntityTypeStore, acts: ActionStore, reqty: RequestType) {

    function inferPermissive(e: Expr, effs: Effects): types.Result<(Type,Effects)> {
      Typechecker(ets,acts,reqty, ValidationMode.Permissive).infer(e,effs)
    }

    function inferStrict(e: Expr, effs: Effects): (res: Result<(Type,Effects)>)
      ensures res.Ok? ==> inferPermissive(e,effs).Ok?
      ensures res.Ok? ==> res.value == inferPermissive(e,effs).value
    {
      // call permissive typechecker
      match inferPermissive(e,effs) {
        // if permissive typechecker returned an error, propagate that error
        case Err(err) => Result.Err(TypeError(err))
        // if the result is True or False, perform no further checks
        case Ok((Bool(True),effs0)) => Result.Ok((Type.Bool(True),effs0))
        case Ok((Bool(False),effs0)) => Result.Ok((Type.Bool(False),effs0))
        // otherwise, perform strict checks and return the result of permissive typechecking
        case Ok((ty,effs0)) =>
          match e {
            case PrimitiveLit(_) | Var(_) => Result.Ok((ty,effs0))
            case If(e1, e2, e3) =>
              var (ty1,effs1) :- inferStrict(e1,effs);
              match ty1 {
                case Bool(True) =>
                  // ignore "else" branch
                  var _ :- inferStrict(e2,effs.union(effs1));
                  Result.Ok((ty,effs0))
                case Bool(False) =>
                  // ignore "then" branch
                  var _ :- inferStrict(e3,effs);
                  Result.Ok((ty,effs0))
                case _ =>
                  // require the branches to have matching types (no subtyping)
                  var (ty2,effs2) :- inferStrict(e2,effs.union(effs1));
                  var (ty3,effs3) :- inferStrict(e3,effs);
                  var _ :- unify(ty2,ty3);
                  Result.Ok((ty,effs0))
              }
            case And(e1, e2) =>
              var (_,effs1) :- inferStrict(e1,effs);
              var _ :- inferStrict(e2,effs.union(effs1));
              Result.Ok((ty,effs0))
            case Or(e1, e2) =>
              var _ :- inferStrict(e1,effs);
              var _ :- inferStrict(e2,effs);
              Result.Ok((ty,effs0))
            case UnaryApp(_, e1) =>
              var _ :- inferStrict(e1,effs);
              Result.Ok((ty,effs0))
            case BinaryApp(op2, e1, e2) =>
              var (ty1,_) :- inferStrict(e1,effs);
              var (ty2,_) :- inferStrict(e2,effs);
              var _ :- inferStrictBinary(op2, e1, e2, ty1, ty2, effs);
              Result.Ok((ty,effs0))
            case GetAttr(e1, _) =>
              var _ :- inferStrict(e1,effs);
              Result.Ok((ty,effs0))
            case HasAttr(e1, _) =>
              var _ :- inferStrict(e1,effs);
              Result.Ok((ty,effs0))
            case Set(es) =>
              assert ty.Set?;
              if ty.ty.Never?
              then Result.Err(StrictTypeError.EmptySetForbidden)
              else
                var tys :- inferStrictSeq(es,effs);
                // either all elements of the set must match `ty` (no subtyping)
                var consistentTypes := forall i | 0 <= i < |tys| :: unify(tys[i],ty.ty).Ok?;
                // or all elements must be actions with the same namespace
                var allActions := isActionSeq(tys,std.None);
                if consistentTypes || allActions
                then Result.Ok((ty,effs0))
                else Result.Err(TypesMustMatch)
            case Record(es) =>
              var _ :- inferStrictRecord(es,effs);
              Result.Ok((ty,effs0))
            case Call(name, args) =>
              var _ :- inferStrictSeq(args,effs);
              // require literal arguments for string parsing functions, which have a "check" field
              if (name in extFunTypes && extFunTypes[name].check.Some?) ==>
                   forall i | 0 <= i < |args| :: args[i].PrimitiveLit?
              then Result.Ok((ty,effs0))
              else Result.Err(StrictTypeError.NonLitExtConstructor)
          }
      }
    }

    function typecheck(e: Expr, ty: Type): (res: Result<Type>)
      ensures res.Ok? ==> Typechecker(ets,acts,reqty, ValidationMode.Permissive).typecheck(e,ty).Ok?
    {
      var (ty1,_) :- inferStrict(e,Effects.empty());
      match Typechecker(ets,acts,reqty, ValidationMode.Permissive).ensureSubty(ty1,ty) {
        case Ok(_) => Result.Ok(ty1)
        case _ => Result.Err(TypeError(UnexpectedType(ty1)))
      }
    }

    // Check that two types are exactly equal, allowing flexibility for Bool types
    function unify(actual: Type, expected: Type): Result<()> {
      match (actual, expected) {
        case (Bool(bt1), Bool(bt2)) => Result.Ok(())
        case (Set(ty1), Set(ty2)) => unify(ty1, ty2)
        case (Record(rty1), Record(rty2)) =>
          if rty1.attrs.Keys == rty2.attrs.Keys &&
             forall k | k in rty1.attrs.Keys :: unify(rty1.attrs[k].ty,rty2.attrs[k].ty).Ok? && rty1.attrs[k].isRequired == rty2.attrs[k].isRequired
          then Result.Ok(())
          else Result.Err(TypesMustMatch)
        case _ =>
          if actual == expected
          then Result.Ok(())
          else Result.Err(TypesMustMatch)
      }
    }

    function inferStrictSeq(es: seq<Expr>, effs: Effects): Result<seq<Type>> {
      if es == [] then Result.Ok([])
      else
        var (ty,_) :- inferStrict(es[0],effs);
        var tys :- inferStrictSeq(es[1..],effs);
        Result.Ok([ty] + tys)
    }

    function inferStrictRecord(es: seq<(Attr,Expr)>, effs: Effects): Result<()> {
      if es == [] then Result.Ok(())
      else
        var _ :- inferStrict(es[0].1,effs);
        var _ :- inferStrictRecord(es[1..],effs);
        Result.Ok(())
    }

    // check whether every Type in a sequence is an Action entity type with namespace ns
    predicate isActionSeq(es: seq<Type>, ns: Option<seq<base.Id>>) {
      if es == [] then ns.Some?
      else
      if es[0].Entity? && extractEntityType(es[0].lub).Ok?
      then
        var ety := extractEntityType(es[0].lub).value;
        match ns {
          case None => isAction(ety) && isActionSeq(es[1..],std.Some(ety.id.path))
          case Some(ns0) => isAction(ety) && ety.id.path == ns0 && isActionSeq(es[1..],ns)
        }
      else false
    }

    function extractEntityType(lub: EntityLUB): Result<EntityType> {
      match lub {
        case AnyEntity => Result.Err(StrictTypeError.NonSingletonLub)
        case EntityLUB(tys) =>
          def.util.EntityTypeLeqIsTotalOrder();
          var tySeq := def.util.SetToSortedSeq(lub.tys,def.util.EntityTypeLeq);
          if |tySeq| == 1
          then Result.Ok(tySeq[0])
          else Result.Err(StrictTypeError.NonSingletonLub)
      }
    }

    function inferStrictBinary(op2: BinaryOp, e1: Expr, e2: Expr, ty1: Type, ty2: Type, effs: Effects): Result<()>
      requires inferPermissive(BinaryApp(op2,e1,e2),effs).Ok?
      requires inferPermissive(e1,effs).Ok? && inferPermissive(e1,effs).value.0 == ty1
      requires inferPermissive(e2,effs).Ok? && inferPermissive(e2,effs).value.0 == ty2
    {
      match op2 {
        case Eq | ContainsAll | ContainsAny => unify(ty1,ty2)
        case In =>
          assert Typechecker(ets,acts,reqty,ValidationMode.Permissive).inferIn(BinaryApp(BinaryOp.In,e1,e2),e1,e2,effs).Ok?;
          assert Typechecker(ets,acts,reqty,ValidationMode.Permissive).ensureEntityType(e1,effs).Ok?;
          assert ty1.Entity?;
          assert Typechecker(ets,acts,reqty,ValidationMode.Permissive).ensureEntitySetType(e2,effs).Ok?;
          assert ty2.Entity? || ty2.Set?;
          var ety1 :- extractEntityType(ty1.lub);
          if isAction(ety1)
          then Result.Ok(())
          else
            var ety2 :-
              if ty2.Set?
              then
                if ty2.ty.Never?
                then Result.Err(StrictTypeError.EmptySetForbidden)
                else extractEntityType(ty2.ty.lub)
              else extractEntityType(ty2.lub);
            if ets.possibleDescendantOf(ety1, ety2)
            then Result.Ok(())
            else Result.Err(TypesMustMatch)
        case Contains =>
          assert Typechecker(ets,acts,reqty,ValidationMode.Permissive).inferContains(e1,e2,effs).Ok?;
          assert Typechecker(ets,acts,reqty,ValidationMode.Permissive).inferSetType(e1,effs).Ok?;
          assert ty1.Set?;
          unify(ty1.ty, ty2)
        // No extra checks required for remaining operators
        case _ => Result.Ok(())
      }
    }
  }
}
