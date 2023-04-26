include "../def/all.dfy"

module validation.types {
  import opened def.base
  import opened def.core

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
        case (EntityLUB(tys1),EntityLUB(tys2)) => EntityLUB(tys1 + tys2)
        case _ => AnyEntity
      }
    }
  }

  datatype AttrType = AttrType(ty: Type, isRequired: bool)
  type RecordType = map<Attr,AttrType>

  // Each extension function is associated with argument types, a return type,
  // and an optional method that checks input well-formedness.
  datatype ExtFunType = ExtFunType(args: seq<Type>, ret: Type, check: Option<seq<Expr> -> Result<()>>)

  datatype Type =
    Never |
    String |
    Int |
    Bool(BoolType) |
    Set(Type) |
    Record(RecordType) |
    Entity(EntityLUB) |
    Extension(Name)

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
    AllFalse

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
