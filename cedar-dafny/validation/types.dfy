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

module validation.types {
  import opened def.base
  import opened def.core

  // The ValidationMode determines whether to use permissive or strict typechecking
  datatype ValidationMode = Permissive | Strict {
    predicate isStrict() {
      match this {
        case Permissive => false
        case Strict => true
      }
    }
  }

  // --------- Types --------- //

  datatype BoolType = AnyBool | True | False {
    function not(): BoolType {
      match this {
        case AnyBool => AnyBool
        case True => False
        case False => True
      }
    }
  }

  type EntityType = core.EntityType

  predicate isAction(ety: EntityType)
  {
    ety.id.id == Id("Action")
  }

  datatype EntityLUB = AnyEntity | EntityLUB(tys: set<EntityType>) {
    predicate subset(other: EntityLUB) {
      match (this, other) {
        case (_, AnyEntity) => true
        case (EntityLUB(tys1),EntityLUB(tys2)) => tys1 <= tys2
        case _ => false
      }
    }
    predicate disjoint(other: EntityLUB) {
      match (this, other) {
        case (EntityLUB(tys1),EntityLUB(tys2)) => tys1 !! tys2
        case _ => false
      }
    }
    function union(other: EntityLUB): EntityLUB {
      match (this, other) {
        case (EntityLUB(tys1),EntityLUB(tys2)) =>
          // Check if either LUB contains an Action entity type. We do not
          // permit any LUBs that contain different action entity types, so
          // their union is `AnyEntity` if they are not the same action entity
          // type. This also gives `AnyEntity` if they are the same action
          // entity type, but some other entity types in the LUB differ. We
          // never construct non-singleton action EntityLUBs, so this cannot
          // occur.
          if (exists ty1 <- tys1 :: isAction(ty1) || exists ty2 <- tys2 :: isAction(ty2)) && tys1 != tys2
          then AnyEntity
          else EntityLUB(tys1 + tys2)
        case _ => AnyEntity
      }
    }
    predicate specified() {
      EntityLUB? && EntityType.UNSPECIFIED !in tys
    }
  }

  datatype AttrType = AttrType(ty: Type, isRequired: bool)
  datatype AttrsTag = OpenAttributes | ClosedAttributes
  datatype RecordType = RecordType(
    attrs: map<Attr,AttrType>,
    // Indicates whether a value having this record type may have attributes
    // beyond those lists in `attrs` (open), or if it must match `attrs`
    // exactly (closed). In principal, any record type, including an entity
    // attributes record type, may be closed or open, but the type of all record
    // literals and any record type written in the schema is always closed. A
    // least upper bound between record types will tend to be open, but it may
    // be closed if the constituent record types are closed and have exactly the
    // same attributes with a least upper bound existing between corresponding
    // attributes.
    attrsTag: AttrsTag
  ) {
    predicate isOpen() {
      attrsTag.OpenAttributes?
    }

    predicate isStrictType() {
      forall k | k in attrs.Keys :: attrs[k].ty.isStrictType()
    }
  }

  // Each extension function is associated with argument types, a return type,
  // and an optional method that checks input well-formedness.
  datatype ExtFunType = ExtFunType(args: seq<Type>, ret: Type, check: Option<seq<Expr> -> Result<()>>)

  datatype Type =
    Never | // used to type the empty set
    String |
    Int |
    Bool(BoolType) |
    Set(ty: Type) |
    Record(RecordType) |
    Entity(lub: EntityLUB) |
    Extension(Name)
  {
    predicate isStrictType() {
      match this {
        case Never => false
        case String | Int | Bool(_) | Extension(_) => true
        case Set(t) => t.isStrictType()
        case Record(rt) => rt.isStrictType()
        case Entity(lub) => lub.EntityLUB? && |lub.tys| == 1
      }
    }
  }

  datatype SetStringType = SetType(Type) | StringType
  datatype RecordEntityType = Record(RecordType) | Entity(EntityLUB)

  // --------- Typing Errors --------- //

  datatype TypeError =
    LubErr(Type,Type) |
    SubtyErr(Type,Type) |
    UnexpectedType(Type) |
    AttrNotFound(Type,Attr) |
    UnknownEntities(set<EntityType>) |
    ExtensionErr(Expr) |
    EmptyLUB |
    EmptySetForbidden |
    NonLitExtConstructor |
    NonSingletonLub |
    HierarchyNotRespected

  // --------- Local Names for Useful Types --------- //

  type Result<T> = std.Result<T,TypeError>

  function Ok<T>(v: T): Result<T> {
    Result.Ok(v)
  }

  function Err<T>(v: TypeError): Result<T> {
    Result.Err(v)
  }

  type Option<T> = std.Option<T>
}
