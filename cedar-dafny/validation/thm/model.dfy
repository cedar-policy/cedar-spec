include "../../def/all.dfy"
include "../all.dfy"
include "base.dfy"

// This module contains an abstract model for the Cedar evaluator semantics.
module validation.thm.model {
  import opened def
  import opened def.core
  import opened types
  import opened subtyping
  import opened base
  import opened ext

  // ----- Utilities ----- //

  // KeyExists and LastOfKey are helpers about association lists that are used in
  // validation.dfy, so we lift them here.
  // We use these as an abbreviation for the quantifier alternation:
  // exists i :: 0 <= i < |es| && (forall j :: i < j < |es| => ...)
  // This helps dafny prove some of our lemmas about record evaluation and validation.
  ghost predicate KeyExists<K,V>(k: K, es: seq<(K,V)>) {
    exists i :: 0 <= i < |es| && es[i].0 == k
  }

  ghost function {:opaque true} LastOfKey<K,V>(k: K, es: seq<(K,V)>): (res: V)
    requires KeyExists(k,es)
    ensures exists i :: 0 <= i < |es| && es[i].0 == k && es[i].1 == res && (forall j :: i < j < |es| ==> es[j].0 != k)
  {
    if (es[0].0 == k && (forall j :: 0 < j < |es| ==> es[j].0 != k)) then es[0].1 else LastOfKey(k,es[1..])
  }

  lemma InterpretRecordLemmaOk(es: seq<(Attr,Expr)>, r: Request, s: EntityStore)
    requires Evaluator(r,s).interpretRecord(es).Ok?
    ensures forall i :: 0 <= i < |es| ==> es[i].0 in Evaluator(r,s).interpretRecord(es).value.Keys && Evaluator(r,s).interpret(es[i].1).Ok?
    ensures forall k :: k in Evaluator(r,s).interpretRecord(es).value.Keys ==> KeyExists(k,es) && Evaluator(r,s).interpret(LastOfKey(k,es)) == base.Ok(Evaluator(r,s).interpretRecord(es).value[k])
  {}

  lemma InterpretRecordLemmaErr(es: seq<(Attr,Expr)>, r: Request, s: EntityStore)
    requires Evaluator(r,s).interpretRecord(es).Err?
    ensures exists i :: 0 <= i < |es| && Evaluator(r,s).interpret(es[i].1) == base.Err(Evaluator(r,s).interpretRecord(es).error) && (forall j :: 0 <= j < i ==> Evaluator(r,s).interpret(es[j].1).Ok?)
  {}

  lemma InterpretSetLemma(es: seq<Expr>, r: Request, s: EntityStore)
    ensures Evaluator(r,s).interpretSet(es).Ok? ==> forall v :: v in Evaluator(r,s).interpretSet(es).value ==> exists i :: 0 <= i < |es| && Evaluator(r,s).interpret(es[i]) == base.Ok(v)
    ensures (forall e :: e in es ==> Evaluator(r,s).interpret(e).Ok?) ==> Evaluator(r,s).interpretSet(es).Ok?
    ensures (exists i :: 0 <= i < |es| && Evaluator(r,s).interpret(es[i]).Err?) ==> Evaluator(r,s).interpretSet(es).Err?
    ensures Evaluator(r,s).interpretSet(es).Err? <==> exists i :: 0 <= i < |es| && Evaluator(r,s).interpret(es[i]).Err? && (forall j :: 0 <= j < i ==> Evaluator(r,s).interpret(es[j]).Ok?);
    ensures Evaluator(r,s).interpretSet(es).Err? ==> exists i :: 0 <= i < |es| && Evaluator(r,s).interpret(es[i]).Err? && Evaluator(r,s).interpret(es[i]).error == Evaluator(r,s).interpretSet(es).error && (forall j :: 0 <= j < i ==> Evaluator(r,s).interpret(es[j]).Ok?);
  {}

  // An implementation of the SemanticModel trait is a model of Cedar.
  // It consists of two main predicates: InstanceOfType and IsSafe, as well as
  // compatability lemmata about the predicates.
  //
  // IsSafe(r, s, e, t) says that when evaluated with Request `q` and EntityStore `s`,
  // evaluating Expr `e` will result in a Value of type `t`.
  //
  // The compatability lemmata are obtained by taking the Cedar typing rules, and
  // replacing the typing relation with the expression safety relation.
  // For example, in Cedar, when e: Bool and e': False, then e && e': False.
  // This is mirrored by the required lemma `AndRShortSafe`, shown below.
  //
  //  lemma AndRShortSafe(r: Request, s: EntityStore, e: Expr, e': Expr)
  //    requires IsSafe(r,s,e,Type.Bool(AnyBool))
  //    requires IsSafe(r,s,e',Type.Bool(False))
  //    ensures IsSafe(r,s,And(e,e'),Type.Bool(False))
  //
  // Every Cedar typing rule has a related compatability lemma. The upshot of this
  // is that we can prove, by induction on the typing relation e: t, that
  // model.IsSafe(_,_,e,t), for any model: SemanticModel.

  // The SemanticModel construction can also be thought of as a way of axiomatizing
  // the behavior of the evaluator that's necessary to prove soundness. When we
  // prove soundness, hiding these properties behind the axiomatic interface
  // of a trait improves the performance of the Dafny verifier significantly.
  trait SemanticModel {
    ghost predicate IsSafe(r: Request, s: EntityStore, e: Expr, t: Type)

    // stronger version of `IsSafe` that disallows errors
    ghost predicate IsSafeStrong(r: Request, s: EntityStore, e: Expr, t: Type)

    // useful shorthands
    ghost predicate IsTrue (r: Request, s: EntityStore, e: Expr) {
      IsSafe(r,s,e,Type.Bool(True))
    }
    ghost predicate IsFalse (r: Request, s: EntityStore, e: Expr) {
      IsSafe(r,s,e,Type.Bool(False))
    }
    ghost predicate GetAttrSafe (r: Request, s: EntityStore, e: Expr, k: Attr) {
      IsTrue(r,s,HasAttr(e,k))
    }
    ghost predicate IsTrueStrong (r: Request, s: EntityStore, e: Expr) {
      IsSafeStrong(r,s,e,Type.Bool(True))
    }
    ghost predicate IsFalseStrong (r: Request, s: EntityStore, e: Expr) {
      IsSafeStrong(r,s,e,Type.Bool(False))
    }

    lemma IsTrueStrongImpliesIsTrue(r: Request, s: EntityStore, e: Expr)
      requires IsTrueStrong(r,s,e)
      ensures IsTrue(r,s,e)

    lemma IsTrueImpliesIsTrueStrong(r: Request, s: EntityStore, e: Expr, t: Type)
      requires IsSafeStrong(r,s,e,t)
      requires IsTrue(r,s,e)
      ensures IsTrueStrong(r,s,e)

    lemma NotTrueImpliesFalse(r: Request, s: EntityStore, e: Expr, bt: BoolType)
      requires IsSafe(r,s,e,Type.Bool(bt))
      requires !IsTrue(r,s,e)
      ensures IsFalse(r,s,e)

    lemma FalseImpliesNotTrueStrong(r: Request, s: EntityStore, e: Expr)
      requires IsFalse(r,s,e)
      ensures !IsTrueStrong(r,s,e)

    ghost predicate SemanticSubty(t1: Type, t2: Type) {
      forall v :: InstanceOfType(v,t1) ==> InstanceOfType(v,t2)
    }

    ghost predicate SemanticUB(t1: Type, t2: Type, ub: Type) {
      SemanticSubty(t1,ub) && SemanticSubty(t2,ub)
    }

    lemma SubtyCompat(t1: Type, t2: Type)
      requires subty(t1,t2)
      ensures SemanticSubty(t1,t2)

    lemma SemSubtyTransportVal(t: Type, t': Type, v: Value)
      requires SemanticSubty(t,t')
      requires InstanceOfType(v,t)
      ensures InstanceOfType(v,t')
    {}

    lemma SemSubtyTransport(r: Request, s: EntityStore, e: Expr, t: Type, t': Type)
      requires SemanticSubty(t,t')
      requires IsSafe(r,s,e,t)
      ensures IsSafe(r,s,e,t')

    lemma PrincipalIsSafe(r: Request, s: EntityStore, t: Type)
      requires InstanceOfType(Value.EntityUID(r.principal),t)
      ensures IsSafe(r,s,Var(Principal),t)

    lemma ActionIsSafe(r: Request, s: EntityStore, t: Type)
      requires InstanceOfType(Value.EntityUID(r.action),t)
      ensures IsSafe(r,s,Var(Action),t)

    lemma ResourceIsSafe(r: Request, s: EntityStore, t: Type)
      requires InstanceOfType(Value.EntityUID(r.resource),t)
      ensures IsSafe(r,s,Var(Resource),t)

    lemma ContextIsSafe(r: Request, s: EntityStore, t: Type)
      requires InstanceOfType(Value.Record(r.context),t)
      ensures IsSafe(r,s,Var(Context),t)

    lemma PrimSafeLift(r: Request, s: EntityStore, p: Primitive, t: Type)
      requires InstanceOfType(Value.Primitive(p),t)
      ensures IsSafe(r,s,Expr.PrimitiveLit(p),t)

    lemma PrimSafeAtInferredType(p: Primitive)
      ensures InstanceOfType(Value.Primitive(p),typeOfPrim(p))

    lemma EqIsSafe(r: Request, s: EntityStore, e: Expr, e': Expr, t: Type, t': Type)
      requires IsSafe(r,s,e,t)
      requires IsSafe(r,s,e',t')
      ensures IsSafe(r,s,BinaryApp(BinaryOp.Eq,e,e'),Type.Bool(AnyBool))

    lemma EqFalseIsSafe(r: Request, s: EntityStore, e: Expr, e': Expr, lub: EntityLUB, lub': EntityLUB)
      requires IsSafe(r,s,e,Type.Entity(lub))
      requires IsSafe(r,s,e',Type.Entity(lub'))
      requires lub.disjoint(lub')
      ensures IsFalse(r,s,BinaryApp(BinaryOp.Eq,e,e'))

    lemma EqEntitySameSafe(r: Request, s: EntityStore, E: EntityUID)
      ensures IsTrue(r,s,Expr.BinaryApp(BinaryOp.Eq,PrimitiveLit(Primitive.EntityUID(E)),PrimitiveLit(Primitive.EntityUID(E))))

    lemma EqEntityDiffSafe(r: Request, s: EntityStore, E: EntityUID, E': EntityUID)
      requires E != E'
      ensures IsFalse(r,s,Expr.BinaryApp(BinaryOp.Eq,PrimitiveLit(Primitive.EntityUID(E)),PrimitiveLit(Primitive.EntityUID(E'))))

    lemma AndLShortSafe(r: Request, s: EntityStore, e: Expr, e': Expr)
      requires IsFalse(r,s,e)
      ensures IsFalse(r,s,And(e,e'))

    lemma AndRShortSafe(r: Request, s: EntityStore, e: Expr, e': Expr)
      requires IsSafe(r,s,e,Type.Bool(AnyBool))
      requires IsFalse(r,s,e')
      ensures IsFalse(r,s,And(e,e'))

    lemma AndLRetSafe(r: Request, s: EntityStore, e: Expr, e': Expr, t: Type)
      requires IsSafe(r,s,e,t)
      requires IsTrue(r,s,e')
      requires SemanticSubty(t,Type.Bool(AnyBool))
      ensures IsSafe(r,s,And(e,e'),t)

    lemma AndSafe(r: Request, s: EntityStore, e: Expr, e': Expr)
      requires IsSafe(r,s,e,Type.Bool(AnyBool))
      requires IsSafe(r,s,e',Type.Bool(AnyBool))
      ensures IsSafe(r,s,And(e,e'),Type.Bool(AnyBool))

    lemma AndTrueStrong(r: Request, s: EntityStore, e1: Expr, e2: Expr)
      requires IsTrue(r,s,e1)
      requires IsTrueStrong(r,s,And(e1,e2))
      ensures IsTrueStrong(r,s,e2)

    lemma AndError(r: Request, s: EntityStore, e1: Expr, e2: Expr, t: Type, tnew: Type)
      requires IsSafe(r,s,e1,t)
      requires !IsSafeStrong(r,s,e1,t)
      ensures IsSafe(r,s,And(e1,e2),tnew)
      ensures !IsSafeStrong(r,s,And(e1,e2),tnew)

    lemma OrLShortSafe(r: Request, s: EntityStore, e: Expr, e': Expr)
      requires IsTrue(r,s,e)
      ensures IsTrue(r,s,Or(e,e'))

    lemma OrRShortSafe(r: Request, s: EntityStore, e: Expr, e': Expr)
      requires IsSafe(r,s,e,Type.Bool(AnyBool))
      requires IsTrue(r,s,e')
      ensures IsTrue(r,s,Or(e,e'))

    lemma OrLRetSafe(r: Request, s: EntityStore, e: Expr, e': Expr, t: Type)
      requires IsSafe(r,s,e,t)
      requires IsFalse(r,s,e')
      requires SemanticSubty(t,Type.Bool(AnyBool))
      ensures IsSafe(r,s,Or(e,e'),t)

    lemma OrRRetSafe(r: Request, s: EntityStore, e: Expr, e': Expr, t: Type)
      requires IsFalse(r,s,e)
      requires IsSafe(r,s,e',t)
      requires SemanticSubty(t,Type.Bool(AnyBool))
      ensures IsSafe(r,s,Or(e,e'),t)

    lemma OrSafe(r: Request, s: EntityStore, e: Expr, e': Expr)
      requires IsSafe(r,s,e,Type.Bool(AnyBool))
      requires IsSafe(r,s,e',Type.Bool(AnyBool))
      ensures IsSafe(r,s,Or(e,e'),Type.Bool(AnyBool))

    lemma OrTrueStrong(r: Request, s: EntityStore, e1: Expr, e2: Expr)
      requires IsTrueStrong(r,s,Or(e1,e2))
      ensures IsTrueStrong(r,s,e1) || IsTrueStrong(r,s,e2)

    lemma NotTrueSafe(r: Request, s: EntityStore, e: Expr)
      requires IsTrue(r,s,e)
      ensures IsFalse(r,s,UnaryApp(Not,e))

    lemma NotFalseSafe(r: Request, s: EntityStore, e: Expr)
      requires IsFalse(r,s,e)
      ensures IsTrue(r,s,UnaryApp(Not,e))

    lemma NotSafe(r: Request, s: EntityStore, e: Expr)
      requires IsSafe(r,s,e,Type.Bool(AnyBool))
      ensures IsSafe(r,s,UnaryApp(Not,e),Type.Bool(AnyBool))

    lemma NegSafe(r: Request, s: EntityStore, e: Expr)
      requires IsSafe(r,s,e,Type.Int)
      ensures IsSafe(r,s,UnaryApp(Neg,e),Type.Int)

    lemma MulBySafe(r: Request, s: EntityStore, e: Expr, i: int)
      requires IsSafe(r,s,e,Type.Int)
      ensures IsSafe(r,s,UnaryApp(MulBy(i),e),Type.Int)

    lemma IteTrueSafe(r: Request, s: EntityStore, e: Expr, e1: Expr, e2: Expr, t: Type)
      requires IsTrue(r,s,e)
      requires IsSafe(r,s,e1,t)
      ensures IsSafe(r,s,If(e,e1,e2),t)

    lemma IteFalseSafe(r: Request, s: EntityStore, e: Expr, e1: Expr, e2: Expr, t: Type)
      requires IsFalse(r,s,e)
      requires IsSafe(r,s,e2,t)
      ensures IsSafe(r,s,If(e,e1,e2),t)

    lemma IteTrueStrongTrue(r: Request, s: EntityStore, e1: Expr, e2: Expr, e3: Expr)
      requires IsTrue(r,s,e1)
      requires IsTrueStrong(r,s,If(e1,e2,e3))
      ensures IsTrueStrong(r,s,e2)

    lemma IteTrueStrongFalse(r: Request, s: EntityStore, e1: Expr, e2: Expr, e3: Expr)
      requires IsFalse(r,s,e1)
      requires IsTrueStrong(r,s,If(e1,e2,e3))
      ensures IsTrueStrong(r,s,e3)

    lemma IteError(r: Request, s: EntityStore, e1: Expr, e2: Expr, e3: Expr, t: Type, tnew: Type)
      requires IsSafe(r,s,e1,t)
      requires !IsSafeStrong(r,s,e1,t)
      ensures IsSafe(r,s,If(e1,e2,e3),tnew)
      ensures !IsSafeStrong(r,s,If(e1,e2,e3),tnew)

    lemma ContainsSetSafe(r: Request, s: EntityStore, e: Expr, e': Expr, t1: Type, t2: Type)
      requires IsSafe(r,s,e,Type.Set(t1))
      requires IsSafe(r,s,e',t2)
      ensures IsSafe(r,s,BinaryApp(Contains,e,e'),Type.Bool(AnyBool))

    lemma LikeSafe(r: Request, s: EntityStore, e: Expr, p: Pattern)
      requires IsSafe(r,s,e,Type.String)
      ensures IsSafe(r,s,UnaryApp(Like(p),e),Type.Bool(AnyBool))

    lemma SetConstrSafe(r: Request, s: EntityStore, es: seq<Expr>, t: Type)
      requires forall i :: 0 <= i < |es| ==> IsSafe(r,s,es[i],t)
      ensures IsSafe(r,s,Expr.Set(es),Type.Set(t))

    lemma ContainsAnyAllSafe(r: Request, s: EntityStore, op: BinaryOp, e1: Expr, e2: Expr, t1: Type, t2: Type)
      requires op == ContainsAll || op == ContainsAny
      requires IsSafe(r,s,e1,Type.Set(t1))
      requires IsSafe(r,s,e2,Type.Set(t2))
      ensures IsSafe(r,s,BinaryApp(op,e1,e2), Type.Bool(AnyBool))

    lemma IneqSafe(r: Request, s: EntityStore, op: BinaryOp, e1: Expr, e2: Expr)
      requires op == Less || op == BinaryOp.LessEq
      requires IsSafe(r,s,e1,Type.Int)
      requires IsSafe(r,s,e2,Type.Int)
      ensures IsSafe(r,s,BinaryApp(op,e1,e2),Type.Bool(AnyBool))

    lemma ArithSafe(r: Request, s: EntityStore, op: BinaryOp, e1: Expr, e2: Expr)
      requires op == Add || op == Sub
      requires IsSafe(r,s,e1,Type.Int)
      requires IsSafe(r,s,e2,Type.Int)
      ensures IsSafe(r,s,BinaryApp(op,e1,e2),Type.Int)

    lemma CallSafe(r: Request, s: EntityStore, name: base.Name, args: seq<Expr>)
      requires name in extFunTypes
      requires |args| == |extFunTypes[name].args|
      requires forall i | 0 <= i < |args| :: IsSafe(r,s,args[i],extFunTypes[name].args[i])
      ensures IsSafe(r,s,Call(name,args),extFunTypes[name].ret)

    lemma RecordSafe(r: Request, s: EntityStore, es: seq<(Attr,Expr)>, rt: RecordType)
      //every entry has some type
      requires forall ae :: ae in es ==> exists t :: IsSafe(r,s,ae.1,t)
      //and the last instance of every required key is safe at the correct type.
      requires forall k :: k in rt ==> KeyExists(k,es) && IsSafe(r,s,LastOfKey(k,es),rt[k].ty)
      ensures IsSafe(r,s,Expr.Record(es),Type.Record(rt))

    lemma ObjectProjSafeRequired(r: Request, s: EntityStore, e: Expr, t: Type, l: Attr, t': AttrType)
      requires IsSafe(r,s,e,t)
      requires SemanticSubty(t,Type.Record(map[l := t']))
      requires t'.isRequired
      ensures IsSafe(r,s,GetAttr(e,l),t'.ty)

    lemma ObjectProjSafeGetAttrSafe(r: Request, s: EntityStore, e: Expr, t: Type, l: Attr, t': AttrType)
      requires IsSafe(r,s,e,t)
      requires SemanticSubty(t,Type.Record(map[l := t']))
      requires GetAttrSafe(r,s,e,l)
      ensures IsSafe(r,s,GetAttr(e,l),t'.ty)

    ghost predicate ExistingEntityInLub(s: EntityStore, ev: EntityUID, lub: EntityLUB) {
      InstanceOfType(Value.Primitive(Primitive.EntityUID(ev)),Type.Entity(lub)) && ev in s.entities
    }

    ghost predicate EntityProjStoreCondition(s: EntityStore, l: Attr, lub: EntityLUB, t': Type, isRequired: bool) {
      forall ev: EntityUID | ExistingEntityInLub(s, ev, lub) ::
        (isRequired ==> l in s.entities[ev].attrs) &&
        (l in s.entities[ev].attrs ==> InstanceOfType(s.entities[ev].attrs[l],t'))
    }

    lemma EntityProjSafe(r: Request, s: EntityStore, e: Expr, l: Attr, lub: EntityLUB, t': Type, isRequired: bool)
      requires IsSafe(r,s,e,Type.Entity(lub))
      requires EntityProjStoreCondition(s, l, lub, t', isRequired)
      requires isRequired || GetAttrSafe(r,s,e,l)
      ensures IsSafe(r,s,GetAttr(e,l),t')

    lemma RecordHasRequiredTrueSafe(r: Request, s: EntityStore, e: Expr, l: Attr, t: AttrType)
      requires IsSafe(r,s,e,Type.Record(map[l := t]))
      requires t.isRequired
      ensures IsTrue(r,s,HasAttr(e,l))

    lemma RecordHasOpenRecSafe(r: Request, s: EntityStore, e: Expr, l: Attr)
      requires IsSafe(r,s,e,Type.Record(map[]))
      ensures IsSafe(r,s,HasAttr(e,l),Type.Bool(AnyBool))

    lemma EntityHasImpossibleFalseSafe(r: Request, s: EntityStore, e: Expr, l: Attr, lub: EntityLUB)
      requires IsSafe(r,s,e,Type.Entity(lub))
      requires forall ev: EntityUID | ExistingEntityInLub(s, ev, lub) ::
                 l !in s.entities[ev].attrs
      ensures IsFalse(r,s,HasAttr(e,l))

    lemma EntityHasOpenSafe(r: Request, s: EntityStore, e: Expr, l: Attr)
      requires IsSafe(r,s,e,Type.Entity(AnyEntity))
      ensures IsSafe(r,s,HasAttr(e,l),Type.Bool(AnyBool))

    lemma InSingleSafe(r: Request, s: EntityStore, e1: Expr, e2: Expr)
      requires IsSafe(r,s,e1,Type.Entity(AnyEntity))
      requires IsSafe(r,s,e2,Type.Entity(AnyEntity))
      ensures IsSafe(r,s,BinaryApp(BinaryOp.In,e1,e2),Type.Bool(AnyBool))

    // Duplicate Evaluator.EntityInEntity here so that SemanticModel and
    // soundness.dfy don't have to depend on engine.dfy.
    ghost predicate EntityInEntity(s: EntityStore, u1: EntityUID, u2: EntityUID) {
      u1 == u2 || (s.getEntityAttrs(u1).Ok? && s.entityIn(u1, u2))
    }

    lemma InSingleFalseLiterals(r: Request, s: EntityStore, u1: EntityUID, u2: EntityUID)
      requires !EntityInEntity(s,u1,u2)
      ensures IsFalse(r,s,BinaryApp(BinaryOp.In,PrimitiveLit(Primitive.EntityUID(u1)),PrimitiveLit(Primitive.EntityUID(u2))))

    lemma InSingleFalseEntityTypeAndLiteral(r: Request, s: EntityStore, e1: Expr, et1: EntityType, u2: EntityUID)
      requires IsSafe(r,s,e1,Type.Entity(EntityLUB({et1})))
      requires forall u1: EntityUID | u1.ty == et1 :: !EntityInEntity(s,u1,u2)
      ensures IsFalse(r,s,BinaryApp(BinaryOp.In,e1,PrimitiveLit(Primitive.EntityUID(u2))))

    lemma InSingleFalseTypes(r: Request, s: EntityStore, e1: Expr, e2: Expr, t1: Type, t2: Type)
      requires subty(t1,Type.Entity(AnyEntity))
      requires subty(t2,Type.Entity(AnyEntity))
      requires IsSafe(r,s,e1,t1)
      requires IsSafe(r,s,e2,t2)
      requires forall u1, u2: EntityUID |
        InstanceOfType(Value.EntityUID(u1), t1) && InstanceOfType(Value.EntityUID(u2), t2) ::
        !EntityInEntity(s,u1,u2)
      ensures IsFalse(r,s,BinaryApp(BinaryOp.In,e1,e2))

    lemma InSetSafe(r: Request, s: EntityStore, e1: Expr, e2: Expr)
      requires IsSafe(r,s,e1,Type.Entity(AnyEntity))
      requires IsSafe(r,s,e2,Type.Set(Type.Entity(AnyEntity)))
      ensures IsSafe(r,s,BinaryApp(BinaryOp.In,e1,e2),Type.Bool(AnyBool))

    lemma InSetFalseIfAllFalse(r: Request, s: EntityStore, e1: Expr, e2s: seq<Expr>)
      requires IsSafe(r,s,e1,Type.Entity(AnyEntity))
      requires forall i | 0 <= i < |e2s| ::
                 IsSafe(r,s,e2s[i],Type.Entity(AnyEntity)) &&
                 IsFalse(r,s,BinaryApp(BinaryOp.In,e1,e2s[i]))
      ensures IsFalse(r,s,BinaryApp(BinaryOp.In,e1,Expr.Set(e2s)))

    lemma InSetFalseTypes(r: Request, s: EntityStore, e1: Expr, e2: Expr, t1: Type, t2: Type)
      requires subty(t1,Type.Entity(AnyEntity))
      requires subty(t2,Type.Entity(AnyEntity))
      requires IsSafe(r,s,e1,t1)
      requires IsSafe(r,s,e2,Type.Set(t2))
      requires forall u1, u2: EntityUID |
        InstanceOfType(Value.EntityUID(u1), t1) && InstanceOfType(Value.EntityUID(u2), t2) ::
        !EntityInEntity(s,u1,u2)
      ensures IsFalse(r,s,BinaryApp(BinaryOp.In,e1,e2))
  }

  // The particular model we're interested in is the EvaluatorModel, where a term
  // is safe if it evaluates to a safe value or an error that is out-of-scope for
  // the validator.
  import opened def.engine
  class EvaluatorModel extends SemanticModel {
    ghost constructor(){}

    // An expression is safe if it evaluates to a value of the expected type
    // or produces an error of type EntityDoesNotExist or ExtensionError.
    //
    // The validator cannot protect against errors where an entity literal is
    // not defined in the entity store or extension errors, but it can protect
    // against all other types of errors, namely: AttrDoesNotExist, TypeError,
    // ArityMismatchError, NoSuchFunctionError
    ghost predicate IsSafe(r: Request, s: EntityStore, e: Expr, t: Type) {
      Evaluate(e,r,s) == base.Err(base.EntityDoesNotExist) ||
      Evaluate(e,r,s) == base.Err(base.ExtensionError) ||
      (Evaluate(e,r,s).Ok? && InstanceOfType(Evaluate(e,r,s).value,t))
    }

    ghost predicate IsSafeStrong (r: Request, s: EntityStore, e: Expr, t: Type) {
      IsSafe(r,s,e,t) && Evaluate(e,r,s).Ok?
    }

    lemma IsTrueStrongImpliesIsTrue(r: Request, s: EntityStore, e: Expr)
      requires IsTrueStrong(r,s,e)
      ensures IsTrue(r,s,e)
    {}

    lemma IsTrueImpliesIsTrueStrong(r: Request, s: EntityStore, e: Expr, t: Type)
      requires IsSafeStrong(r,s,e,t)
      requires IsTrue(r,s,e)
      ensures IsTrueStrong(r,s,e)
    {}

    lemma NotTrueImpliesFalse(r: Request, s: EntityStore, e: Expr, bt: BoolType)
      requires IsSafe(r,s,e,Type.Bool(bt))
      requires !IsTrue(r,s,e)
      ensures IsFalse(r,s,e)
    {}

    lemma NotSafeImpliesNotSafeStrong(r: Request, s: EntityStore, e: Expr, t: Type)
      requires !IsSafe(r,s,e,t)
      ensures !IsSafeStrong(r,s,e,t)
    {}

    lemma FalseImpliesNotTrueStrong(r: Request, s: EntityStore, e: Expr)
      requires IsFalse(r,s,e)
      ensures !IsTrueStrong(r,s,e)
    {}

    lemma SubtyCompat(t: Type, t': Type)
      requires subty(t,t')
      ensures SemanticSubty(t,t')
    {
      assert subty(t,t');
      assert SemanticSubty(t,t') by {
        forall v: Value | InstanceOfType(v,t)
          ensures InstanceOfType(v,t')
        {
          SubtyCompatPointwise(t,t',v);
        }
      }
    }

    lemma SubtyCompatMatchPointwise(t: Type, t': Type, v: Value)
      requires subty(t,t')
      requires InstanceOfType(v,t)
      ensures InstanceOfType(v,t')
      decreases t
    {
      match (t,t',v) {
        case (Never,_,_) =>
        case (String,String,_) =>
        case (Int,Int,_) =>
        case (Bool(b1),Bool(b2),_) =>
        case (Set(t1),Set(t2),Set(s)) =>
          assert forall v' | v' in s :: InstanceOfType(v',t2) by {
            forall v': Value | v' in s
              ensures InstanceOfType(v',t2)
            {
              assert InstanceOfType(v',t1);
              SubtyCompatMatchPointwise(t1,t2,v');
            }
          }
        case (Record(rt1),Record(rt2),Record(rv)) =>
          assert forall k | k in rt2 && k in rv :: InstanceOfType(rv[k],rt2[k].ty) by {
            forall k: Attr | k in rt2 && k in rv
              ensures InstanceOfType(rv[k],rt2[k].ty)
            {
              assert InstanceOfType(rv[k],rt1[k].ty);
              assert subtyAttrType(rt1[k],rt2[k]);
              SubtyCompatMatchPointwise(rt1[k].ty,rt2[k].ty,rv[k]);
            }
          }
          assert forall k | k in rt2 && rt2[k].isRequired :: k in rv by {
            forall k | k in rt2 && rt2[k].isRequired
              ensures k in rv
            {
              assert subtyAttrType(rt1[k],rt2[k]);
            }
          }
        case (Entity(e1),Entity(e2),_) =>
        case (Extension(e1),Extension(e2),_) =>
      }
    }

    lemma SubtyCompatPointwise(t: Type, t': Type, v: Value)
      requires subty(t,t')
      requires InstanceOfType(v,t)
      ensures InstanceOfType(v,t')
    {
      SubtyCompatMatchPointwise(t,t',v);
    }

    lemma SemSubtyTransport(r: Request, s: EntityStore, e: Expr, t: Type, t': Type)
      requires SemanticSubty(t,t')
      requires IsSafe(r,s,e,t)
      ensures IsSafe(r,s,e,t')
    {
      if (exists v :: Evaluate(e,r,s) == base.Ok(v) && InstanceOfType(v,t)) {
        var v :| Evaluate(e,r,s) == base.Ok(v) && InstanceOfType(v,t);
        assert InstanceOfType(v,t') by {
          SemSubtyTransportVal(t,t',v);
        }
      }
    }

    lemma PrincipalIsSafe(r: Request, s: EntityStore, t: Type)
      requires InstanceOfType(Value.EntityUID(r.principal),t)
      ensures IsSafe(r,s,Var(Principal),t)
    {}

    lemma ActionIsSafe(r: Request, s: EntityStore, t: Type)
      requires InstanceOfType(Value.EntityUID(r.action),t)
      ensures IsSafe(r,s,Var(Action),t)
    {}

    lemma ResourceIsSafe(r: Request, s: EntityStore, t: Type)
      requires InstanceOfType(Value.EntityUID(r.resource),t)
      ensures IsSafe(r,s,Var(Resource),t)
    {}

    lemma ContextIsSafe(r: Request, s: EntityStore, t: Type)
      requires InstanceOfType(Value.Record(r.context),t)
      ensures IsSafe(r,s,Var(Context),t)
    {}

    lemma PrimSafeLift(r: Request, s: EntityStore, p: Primitive, t: Type)
      requires InstanceOfType(Value.Primitive(p),t)
      ensures IsSafe(r,s,Expr.PrimitiveLit(p),t)
    {}

    lemma PrimSafeAtInferredType(p: Primitive)
      ensures InstanceOfType(Value.Primitive(p),typeOfPrim(p))
    {}

    lemma EqIsSafe(r: Request, s: EntityStore, e: Expr, e': Expr, t: Type, t': Type)
      requires IsSafe(r,s,e,t)
      requires IsSafe(r,s,e',t')
      ensures IsSafe(r,s,BinaryApp(BinaryOp.Eq,e,e'),Type.Bool(AnyBool))
    {}

    lemma EqFalseIsSafe(r: Request, s: EntityStore, e: Expr, e': Expr, lub: EntityLUB, lub': EntityLUB)
      requires IsSafe(r,s,e,Type.Entity(lub))
      requires IsSafe(r,s,e',Type.Entity(lub'))
      requires lub.disjoint(lub')
      ensures IsFalse(r,s,BinaryApp(BinaryOp.Eq,e,e'))
    {}

    lemma EqEntitySameSafe(r: Request, s: EntityStore, E: EntityUID)
      ensures IsTrue(r,s,Expr.BinaryApp(BinaryOp.Eq,PrimitiveLit(Primitive.EntityUID(E)),PrimitiveLit(Primitive.EntityUID(E))))
    {
      var e := Expr.BinaryApp(BinaryOp.Eq,PrimitiveLit(Primitive.EntityUID(E)),PrimitiveLit(Primitive.EntityUID(E)));
      assert Evaluator(r,s).interpret(e) == base.Ok(Value.Primitive(Primitive.Bool(true)));
    }

    lemma EqEntityDiffSafe(r: Request, s: EntityStore, E: EntityUID, E': EntityUID)
      requires E != E'
      ensures IsFalse(r,s,Expr.BinaryApp(BinaryOp.Eq,PrimitiveLit(Primitive.EntityUID(E)),PrimitiveLit(Primitive.EntityUID(E'))))
    {
      var e := Expr.BinaryApp(BinaryOp.Eq,PrimitiveLit(Primitive.EntityUID(E)),PrimitiveLit(Primitive.EntityUID(E')));
      assert Evaluator(r,s).interpret(e) == base.Ok(Value.Primitive(Primitive.Bool(false)));
    }

    lemma AndLShortSafe(r: Request, s: EntityStore, e: Expr, e': Expr)
      requires IsFalse(r,s,e)
      ensures IsFalse(r,s,And(e,e'))
    {
      if Evaluate(e,r,s).Ok? {
        assert Evaluate(e,r,s) == base.Ok(Value.Primitive(Primitive.Bool(false)));
        assert Evaluator(r,s).interpretShortcircuit(And(e,e'),e,e',false) == base.Ok(Value.Primitive(Primitive.Bool(false)));
        assert Evaluate(And(e,e'),r,s) == base.Ok(Value.Primitive(Primitive.Bool(false)));
      } else {
        assert Evaluator(r,s).interpretShortcircuit(And(e,e'),e,e',false) == Evaluate(e,r,s);
        assert Evaluate(And(e,e'),r,s) == Evaluate(e,r,s);
      }
    }

    lemma AndRShortSafe(r: Request, s: EntityStore, e: Expr, e': Expr)
      requires IsSafe(r,s,e,Type.Bool(AnyBool))
      requires IsFalse(r,s,e')
      ensures IsFalse(r,s,And(e,e'))
    {
      if Evaluate(e,r,s).Ok? && Evaluate(e',r,s).Ok? {
        assert Evaluate(e',r,s) == base.Ok(Value.Primitive(Primitive.Bool(false)));
        assert Evaluator(r,s).interpretShortcircuit(And(e,e'),e,e',false) == base.Ok(Value.Primitive(Primitive.Bool(false)));
        assert Evaluate(And(e,e'),r,s) == base.Ok(Value.Primitive(Primitive.Bool(false)));
      } else {
        if Evaluate(e,r,s).Err? {
          assert Evaluator(r,s).interpretShortcircuit(And(e,e'),e,e',false) == Evaluate(e,r,s);
          assert Evaluate(And(e,e'),r,s) == Evaluate(e,r,s);
        } else {
          assert Evaluate(e',r,s).Err?;
          var b :| Evaluate(e,r,s) == base.Ok(Value.Primitive(Primitive.Bool(b)));
          if b {
            assert Evaluator(r,s).interpretShortcircuit(And(e,e'),e,e',false) == Evaluate(e',r,s);
            assert Evaluate(And(e,e'),r,s) == Evaluate(e',r,s);
          } else {
            assert Evaluator(r,s).interpretShortcircuit(And(e,e'),e,e',false) == base.Ok(Value.Primitive(Primitive.Bool(false)));
            assert Evaluate(And(e,e'),r,s) == base.Ok(Value.Primitive(Primitive.Bool(false)));
          }
        }
      }
    }

    lemma AndLRetSafe(r: Request, s: EntityStore, e: Expr, e': Expr, t: Type)
      requires IsSafe(r,s,e,t)
      requires IsTrue(r,s,e')
      requires SemanticSubty(t,Type.Bool(AnyBool))
      ensures IsSafe(r,s,And(e,e'),t)
    {
      if Evaluate(e,r,s).Ok? && Evaluate(e',r,s).Ok? {
        assert Evaluate(e',r,s) == base.Ok(Value.Primitive(Primitive.Bool(true)));
        var v :| Evaluate(e,r,s) == base.Ok(v) && InstanceOfType(v,t);
        assert InstanceOfType(v,Type.Bool(AnyBool)) by {
          SemSubtyTransportVal(t,Type.Bool(AnyBool),v);
        }
        var b :| v == Value.Primitive(Primitive.Bool(b));
        assert Evaluator(r,s).interpretShortcircuit(And(e,e'),e,e',false) == base.Ok(Value.Primitive(Primitive.Bool(b)));
        assert Evaluate(And(e,e'),r,s) == base.Ok(Value.Primitive(Primitive.Bool(b)));
      } else {
        if Evaluate(e,r,s).Err? {
          assert Evaluator(r,s).interpretShortcircuit(And(e,e'),e,e',false) == Evaluate(e,r,s);
          assert Evaluate(And(e,e'),r,s) == Evaluate(e,r,s);
        } else {
          assert Evaluate(e',r,s).Err?;
          var b :| Evaluate(e,r,s) == base.Ok(Value.Primitive(Primitive.Bool(b)));
          if b {
            assert Evaluator(r,s).interpretShortcircuit(And(e,e'),e,e',false) == Evaluate(e',r,s);
            assert Evaluate(And(e,e'),r,s) == Evaluate(e',r,s);
          } else {
            assert Evaluator(r,s).interpretShortcircuit(And(e,e'),e,e',false) == base.Ok(Value.Primitive(Primitive.Bool(false)));
            assert Evaluate(And(e,e'),r,s) == base.Ok(Value.Primitive(Primitive.Bool(false)));
          }
        }
      }
    }

    lemma AndSafe(r: Request, s: EntityStore, e: Expr, e': Expr)
      requires IsSafe(r,s,e,Type.Bool(AnyBool))
      requires IsSafe(r,s,e',Type.Bool(AnyBool))
      ensures IsSafe(r,s,And(e,e'),Type.Bool(AnyBool))
    {
      if Evaluate(e,r,s).Ok? && Evaluate(e',r,s).Ok? {
        assert Evaluator(r,s).interpretShortcircuit(And(e,e'),e,e',false).Ok?;
        assert Evaluate(And(e,e'),r,s).Ok?;
      } else {
        if Evaluate(e,r,s).Err? {
          assert Evaluator(r,s).interpretShortcircuit(And(e,e'),e,e',false) == Evaluate(e,r,s);
          assert Evaluate(And(e,e'),r,s) == Evaluate(e,r,s);
        } else {
          assert Evaluate(e',r,s).Err?;
          var b :| Evaluate(e,r,s) == base.Ok(Value.Primitive(Primitive.Bool(b)));
          if b {
            assert Evaluator(r,s).interpretShortcircuit(And(e,e'),e,e',false) == Evaluate(e',r,s);
            assert Evaluate(And(e,e'),r,s) == Evaluate(e',r,s);
          } else {
            assert Evaluator(r,s).interpretShortcircuit(And(e,e'),e,e',false) == base.Ok(Value.Primitive(Primitive.Bool(false)));
            assert Evaluate(And(e,e'),r,s) == base.Ok(Value.Primitive(Primitive.Bool(false)));
          }
        }
      }
    }

    lemma AndTrueStrong(r: Request, s: EntityStore, e1: Expr, e2: Expr)
      requires IsTrue(r,s,e1)
      requires IsTrueStrong(r,s,And(e1,e2))
      ensures IsTrueStrong(r,s,e2)
    {
      assert Evaluator(r,s).interpretShortcircuit(And(e1,e2),e1,e2,false) == base.Ok(Value.Bool(true));
    }

    lemma AndError(r: Request, s: EntityStore, e1: Expr, e2: Expr, t: Type, tnew: Type)
      requires IsSafe(r,s,e1,t)
      requires !IsSafeStrong(r,s,e1,t)
      ensures IsSafe(r,s,And(e1,e2),tnew)
      ensures !IsSafeStrong(r,s,And(e1,e2),tnew)
    {
      assert Evaluator(r,s).interpretShortcircuit(And(e1,e2),e1,e2,false).Err?;
    }

    lemma OrLShortSafe(r: Request, s: EntityStore, e: Expr, e': Expr)
      requires IsTrue(r,s,e)
      ensures IsTrue(r,s,Or(e,e'))
    {
      if Evaluate(e,r,s).Ok? {
        assert Evaluate(e,r,s) == base.Ok(Value.Primitive(Primitive.Bool(true)));
        assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == base.Ok(Value.Primitive(Primitive.Bool(true)));
        assert Evaluate(Or(e,e'),r,s) == base.Ok(Value.Primitive(Primitive.Bool(true)));
      } else {
        assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == Evaluate(e,r,s);
        assert Evaluate(Or(e,e'),r,s) == Evaluate(e,r,s);
      }
    }

    lemma OrRShortSafe(r: Request, s: EntityStore, e: Expr, e': Expr)
      requires IsSafe(r,s,e,Type.Bool(AnyBool))
      requires IsTrue(r,s,e')
      ensures IsTrue(r,s,Or(e,e'))
    {
      if Evaluate(e,r,s).Ok? && Evaluate(e',r,s).Ok? {
        assert Evaluate(e',r,s) == base.Ok(Value.Primitive(Primitive.Bool(true)));
        assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == base.Ok(Value.Primitive(Primitive.Bool(true)));
        assert Evaluate(Or(e,e'),r,s) == base.Ok(Value.Primitive(Primitive.Bool(true)));
      } else {
        if Evaluate(e,r,s).Err? {
          assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == Evaluate(e,r,s);
          assert Evaluate(Or(e,e'),r,s) == Evaluate(e,r,s);
        } else {
          assert Evaluate(e',r,s).Err?;
          var b :| Evaluate(e,r,s) == base.Ok(Value.Primitive(Primitive.Bool(b)));
          if b {
            assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == base.Ok(Value.Primitive(Primitive.Bool(true)));
            assert Evaluate(Or(e,e'),r,s) == base.Ok(Value.Primitive(Primitive.Bool(true)));
          } else {
            assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == Evaluate(e',r,s);
            assert Evaluate(Or(e,e'),r,s) == Evaluate(e',r,s);
          }
        }
      }
    }

    lemma OrLRetSafe(r: Request, s: EntityStore, e: Expr, e': Expr, t: Type)
      requires IsSafe(r,s,e,t)
      requires IsFalse(r,s,e')
      requires SemanticSubty(t,Type.Bool(AnyBool))
      ensures IsSafe(r,s,Or(e,e'),t)
    {
      if Evaluate(e,r,s).Ok? && Evaluate(e',r,s).Ok? {
        assert Evaluate(e',r,s) == base.Ok(Value.Primitive(Primitive.Bool(false)));
        var v :| Evaluate(e,r,s) == base.Ok(v) && InstanceOfType(v,t);
        assert InstanceOfType(v,Type.Bool(AnyBool)) by {
          SemSubtyTransportVal(t,Type.Bool(AnyBool),v);
        }
        var b :| v == Value.Primitive(Primitive.Bool(b));
        assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == base.Ok(Value.Primitive(Primitive.Bool(b)));
        assert Evaluate(Or(e,e'),r,s) == base.Ok(Value.Primitive(Primitive.Bool(b)));
        assert IsSafe(r,s,e,Type.Bool(AnyBool)) by {
          SemSubtyTransport(r,s,e,t,Type.Bool(AnyBool));
        }
      } else {
        if Evaluate(e,r,s).Err? {
          assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == Evaluate(e,r,s);
          assert Evaluate(Or(e,e'),r,s) == Evaluate(e,r,s);
        } else {
          assert Evaluate(e',r,s).Err?;
          var b :| Evaluate(e,r,s) == base.Ok(Value.Primitive(Primitive.Bool(b)));
          if b {
            assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == base.Ok(Value.Primitive(Primitive.Bool(true)));
            assert Evaluate(Or(e,e'),r,s) == base.Ok(Value.Primitive(Primitive.Bool(true)));
          } else {
            assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == Evaluate(e',r,s);
            assert Evaluate(Or(e,e'),r,s) == Evaluate(e',r,s);
          }
        }
      }
    }

    lemma OrRRetSafe(r: Request, s: EntityStore, e: Expr, e': Expr, t: Type)
      requires IsFalse(r,s,e)
      requires IsSafe(r,s,e',t)
      requires SemanticSubty(t,Type.Bool(AnyBool))
      ensures IsSafe(r,s,Or(e,e'),t)
    {
      if Evaluate(e,r,s).Ok? && Evaluate(e',r,s).Ok? {
        assert Evaluate(e,r,s) == base.Ok(Value.Primitive(Primitive.Bool(false)));
        var v :| Evaluate(e',r,s) == base.Ok(v) && InstanceOfType(v,t);
        assert InstanceOfType(v,Type.Bool(AnyBool)) by {
          SemSubtyTransportVal(t,Type.Bool(AnyBool),v);
        }
        var b :| v == Value.Primitive(Primitive.Bool(b));
        assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == base.Ok(Value.Primitive(Primitive.Bool(b)));
        assert Evaluate(Or(e,e'),r,s) == base.Ok(Value.Primitive(Primitive.Bool(b)));
        assert IsSafe(r,s,e',Type.Bool(AnyBool)) by {
          SemSubtyTransport(r,s,e',t,Type.Bool(AnyBool));
        }
      } else {
        if Evaluate(e,r,s).Err? {
          assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == Evaluate(e,r,s);
          assert Evaluate(Or(e,e'),r,s) == Evaluate(e,r,s);
        } else {
          assert Evaluate(e',r,s).Err?;
          var b :| Evaluate(e,r,s) == base.Ok(Value.Primitive(Primitive.Bool(b)));
          if b {
            assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == base.Ok(Value.Primitive(Primitive.Bool(true)));
            assert Evaluate(Or(e,e'),r,s) == base.Ok(Value.Primitive(Primitive.Bool(true)));
          } else {
            assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == Evaluate(e',r,s);
            assert Evaluate(Or(e,e'),r,s) == Evaluate(e',r,s);
          }
        }
      }
    }

    lemma OrSafe(r: Request, s: EntityStore, e: Expr, e': Expr)
      requires IsSafe(r,s,e,Type.Bool(AnyBool))
      requires IsSafe(r,s,e',Type.Bool(AnyBool))
      ensures IsSafe(r,s,Or(e,e'),Type.Bool(AnyBool))
    {
      if Evaluate(e,r,s).Ok? && Evaluate(e',r,s).Ok? {
        assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true).Ok?;
        assert Evaluate(Or(e,e'),r,s).Ok?;
      } else {
        if Evaluate(e,r,s).Err? {
          assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == Evaluate(e,r,s);
          assert Evaluate(Or(e,e'),r,s) == Evaluate(e,r,s);
        } else {
          assert Evaluate(e',r,s).Err?;
          var b :| Evaluate(e,r,s) == base.Ok(Value.Primitive(Primitive.Bool(b)));
          if b {
            assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == base.Ok(Value.Primitive(Primitive.Bool(true)));
            assert Evaluate(Or(e,e'),r,s) == base.Ok(Value.Primitive(Primitive.Bool(true)));
          } else {
            assert Evaluator(r,s).interpretShortcircuit(Or(e,e'),e,e',true) == Evaluate(e',r,s);
            assert Evaluate(Or(e,e'),r,s) == Evaluate(e',r,s);
          }
        }
      }
    }

    lemma OrTrueStrong(r: Request, s: EntityStore, e1: Expr, e2: Expr)
      requires IsTrueStrong(r,s,Or(e1,e2))
      ensures IsTrueStrong(r,s,e1) || IsTrueStrong(r,s,e2)
    {
      assert Evaluator(r,s).interpretShortcircuit(Or(e1,e2),e1,e2,true) == base.Ok(Value.Bool(true));
    }

    lemma NotTrueSafe(r: Request, s: EntityStore, e: Expr)
      requires IsTrue(r,s,e)
      ensures IsFalse(r,s,UnaryApp(Not,e))
    {}

    lemma NotFalseSafe(r: Request, s: EntityStore, e: Expr)
      requires IsFalse(r,s,e)
      ensures IsTrue(r,s,UnaryApp(Not,e))
    {}

    lemma NotSafe(r: Request, s: EntityStore, e: Expr)
      requires IsSafe(r,s,e,Type.Bool(AnyBool))
      ensures IsSafe(r,s,UnaryApp(Not,e),Type.Bool(AnyBool))
    {}

    lemma NegSafe(r: Request, s: EntityStore, e: Expr)
      requires IsSafe(r,s,e,Type.Int)
      ensures IsSafe(r,s,UnaryApp(Neg,e),Type.Int)
    {}

    lemma MulBySafe(r: Request, s: EntityStore, e: Expr, i: int)
      requires IsSafe(r,s,e,Type.Int)
      ensures IsSafe(r,s,UnaryApp(MulBy(i),e),Type.Int)
    {}

    lemma IteTrueSafe(r: Request, s: EntityStore, e: Expr, e1: Expr, e2: Expr, t: Type)
      requires IsTrue(r,s,e)
      requires IsSafe(r,s,e1,t)
      ensures IsSafe(r,s,If(e,e1,e2),t)
    {}

    lemma IteFalseSafe(r: Request, s: EntityStore, e: Expr, e1: Expr, e2: Expr, t: Type)
      requires IsFalse(r,s,e)
      requires IsSafe(r,s,e2,t)
      ensures IsSafe(r,s,If(e,e1,e2),t)
    {}

    lemma IteTrueStrongTrue(r: Request, s: EntityStore, e1: Expr, e2: Expr, e3: Expr)
      requires IsTrue(r,s,e1)
      requires IsTrueStrong(r,s,If(e1,e2,e3))
      ensures IsTrueStrong(r,s,e2)
    {}

    lemma IteTrueStrongFalse(r: Request, s: EntityStore, e1: Expr, e2: Expr, e3: Expr)
      requires IsFalse(r,s,e1)
      requires IsTrueStrong(r,s,If(e1,e2,e3))
      ensures IsTrueStrong(r,s,e3)
    {}

    lemma IteError(r: Request, s: EntityStore, e1: Expr, e2: Expr, e3: Expr, t: Type, tnew: Type)
      requires IsSafe(r,s,e1,t)
      requires !IsSafeStrong(r,s,e1,t)
      ensures IsSafe(r,s,If(e1,e2,e3),tnew)
      ensures !IsSafeStrong(r,s,If(e1,e2,e3),tnew)
    {}

    lemma ContainsSetSafe(r: Request, s: EntityStore, e: Expr, e': Expr, t1: Type, t2: Type)
      requires IsSafe(r,s,e,Type.Set(t1))
      requires IsSafe(r,s,e',t2)
      ensures IsSafe(r,s,BinaryApp(Contains,e,e'),Type.Bool(AnyBool))
    {}

    lemma LikeSafe(r: Request, s: EntityStore, e: Expr, p: Pattern)
      requires IsSafe(r,s,e,Type.String)
      ensures IsSafe(r,s,UnaryApp(Like(p),e),Type.Bool(AnyBool))
    {}

    lemma SetConstrSafe(r: Request, s: EntityStore, es: seq<Expr>, t: Type)
      requires forall i :: 0 <= i < |es| ==> IsSafe(r,s,es[i],t)
      ensures IsSafe(r,s,Expr.Set(es),Type.Set(t))
    {
      InterpretSetLemma(es,r,s);
      if(forall i :: 0 <= i < |es| ==> exists v :: Evaluate(es[i],r,s) == base.Ok(v) && InstanceOfType(v,t)){
        assert forall e :: e in es ==> Evaluate(e,r,s).Ok?;
        assert Evaluate(Expr.Set(es),r,s).Ok?;
        var vs :| Evaluator(r,s).interpretSet(es) == base.Ok(vs);
        assert InstanceOfType(Value.Set(vs),Type.Set(t)) by {
          forall v | v in vs ensures InstanceOfType(v,t) {}
        }
      }
    }

    lemma ContainsAnyAllSafe(r: Request, s: EntityStore, op: BinaryOp, e1: Expr, e2: Expr, t1: Type, t2: Type)
      requires op == ContainsAll || op == ContainsAny
      requires IsSafe(r,s,e1,Type.Set(t1))
      requires IsSafe(r,s,e2,Type.Set(t2))
      ensures IsSafe(r,s,BinaryApp(op,e1,e2), Type.Bool(AnyBool))
    {}

    lemma IneqSafe(r: Request, s: EntityStore, op: BinaryOp, e1: Expr, e2: Expr)
      requires op == Less || op == BinaryOp.LessEq
      requires IsSafe(r,s,e1,Type.Int)
      requires IsSafe(r,s,e2,Type.Int)
      ensures IsSafe(r,s,BinaryApp(op,e1,e2),Type.Bool(AnyBool))
    {}

    lemma ArithSafe(r: Request, s: EntityStore, op: BinaryOp, e1: Expr, e2: Expr)
      requires op == Add || op == Sub
      requires IsSafe(r,s,e1,Type.Int)
      requires IsSafe(r,s,e2,Type.Int)
      ensures IsSafe(r,s,BinaryApp(op,e1,e2),Type.Int)
    {}

    // We prove that every extension function is safe with respect to the
    // ExtFunType assigned to it by the validator. In particular, we show that
    // the argument types of the ExtFunType match the argument type checks
    // actually performed by the function at runtime, the return value has the
    // correct type on success, and the function doesn't raise any error other
    // than ExtensionError.
    //
    // Writing one lemma per extension function would be a lot of boilerplate.
    // Instead, we put them in groups that have the same ExtFunType.

    ghost predicate ExtensionFunSafeRequires(name: base.Name, args: seq<Value>)
      requires name in extFunTypes
    {
      var eft := extFunTypes[name];
      |args| == |eft.args| &&
      forall i | 0 <= i < |args| :: InstanceOfType(args[i], eft.args[i])
    }

    ghost predicate ExtensionFunSafeEnsures(name: base.Name, args: seq<Value>)
      requires name in extFunTypes
    {
      var eft := extFunTypes[name];
      var res := extFuns[name].fun(args);
      res == base.Err(base.ExtensionError) || (res.Ok? && InstanceOfType(res.value, eft.ret))
    }

    ghost predicate IsDecimalConstructorName(name: base.Name) {
      name == base.Name.fromStr("decimal")
    }

    lemma DecimalConstructorSafe(name: base.Name, args: seq<Value>)
      requires IsDecimalConstructorName(name)
      requires ExtensionFunSafeRequires(name, args)
      ensures ExtensionFunSafeEnsures(name, args)
    {}

    ghost predicate IsDecimalComparisonName(name: base.Name) {
      name == base.Name.fromStr("lessThan") ||
      name == base.Name.fromStr("lessThanOrEqual") ||
      name == base.Name.fromStr("greaterThan") ||
      name == base.Name.fromStr("greaterThanOrEqual")
    }

    lemma DecimalComparisonSafe(name: base.Name, args: seq<Value>)
      requires IsDecimalComparisonName(name)
      requires ExtensionFunSafeRequires(name, args)
      ensures ExtensionFunSafeEnsures(name, args)
    {}

    ghost predicate IsIpConstructorName(name: base.Name) {
      name == base.Name.fromStr("ip")
    }

    lemma IpConstructorSafe(name: base.Name, args: seq<Value>)
      requires IsIpConstructorName(name)
      requires ExtensionFunSafeRequires(name, args)
      ensures ExtensionFunSafeEnsures(name, args)
    {}

    ghost predicate IsIpUnaryName(name: base.Name) {
      name == base.Name.fromStr("isIpv4") ||
      name == base.Name.fromStr("isIpv6") ||
      name == base.Name.fromStr("isLoopback") ||
      name == base.Name.fromStr("isMulticast")
    }

    lemma IpUnarySafe(name: base.Name, args: seq<Value>)
      requires IsIpUnaryName(name)
      requires ExtensionFunSafeRequires(name, args)
      ensures ExtensionFunSafeEnsures(name, args)
    {
      assert |args| == 1 && args[0].Extension? && args[0].ex.IPAddr?;
    }

    ghost predicate IsIpBinaryName(name: base.Name) {
      name == base.Name.fromStr("isInRange")
    }

    lemma IpBinarySafe(name: base.Name, args: seq<Value>)
      requires IsIpBinaryName(name)
      requires ExtensionFunSafeRequires(name, args)
      ensures ExtensionFunSafeEnsures(name, args)
    {}

    lemma InterpretListEnsures(eval: Evaluator, es: seq<Expr>)
      ensures eval.interpretList(es).Ok? ==> (|eval.interpretList(es).value| == |es| &&
                                              forall i | 0 <= i < |es| :: eval.interpret(es[i]) == base.Ok(eval.interpretList(es).value[i]))
      ensures (forall e :: e in es ==> eval.interpret(e).Ok?) ==> eval.interpretList(es).Ok?
      ensures (exists i :: 0 <= i < |es| && eval.interpret(es[i]).Err?) ==> eval.interpretList(es).Err?
      ensures eval.interpretList(es).Err? <==> exists i :: 0 <= i < |es| && eval.interpret(es[i]).Err? && (forall j :: 0 <= j < i ==> eval.interpret(es[j]).Ok?)
      ensures eval.interpretList(es).Err? ==> exists i :: 0 <= i < |es| && eval.interpret(es[i]).Err? && eval.interpret(es[i]).error == eval.interpretList(es).error && (forall j :: 0 <= j < i ==> eval.interpret(es[j]).Ok?)
    {}

    lemma CallSafe(r: Request, s: EntityStore, name: base.Name, args: seq<Expr>)
      requires name in extFunTypes
      requires |args| == |extFunTypes[name].args|
      requires forall i | 0 <= i < |args| :: IsSafe(r,s,args[i],extFunTypes[name].args[i])
      ensures IsSafe(r,s,Call(name,args),extFunTypes[name].ret)
    {
      var eft := extFunTypes[name];
      if (forall i | 0 <= i < |args| :: Evaluate(args[i],r,s).Ok?) {
        assert forall e <- args :: Evaluate(e,r,s).Ok?;

        InterpretListEnsures(Evaluator(r, s), args);
        var argVals := Evaluator(r, s).interpretList(args).value;

        var res := Evaluator(r, s).applyExtFun(name, argVals);
        assert Evaluate(Call(name,args),r,s) == res;
        assert forall i | 0 <= i < |args| :: InstanceOfType(argVals[i], eft.args[i]);
        var isSafe := (res == base.Err(base.ExtensionError) || (res.Ok? && InstanceOfType(res.value, eft.ret)));
        if IsDecimalConstructorName(name) {
          DecimalConstructorSafe(name, argVals);
          assert isSafe;
        } else if IsDecimalComparisonName(name) {
          DecimalComparisonSafe(name, argVals);
          assert isSafe;
        } else if IsIpConstructorName(name) {
          IpConstructorSafe(name, argVals);
          assert isSafe;
        } else if IsIpUnaryName(name) {
          IpUnarySafe(name, argVals);
          assert isSafe;
        } else if IsIpBinaryName(name) {
          IpBinarySafe(name, argVals);
          assert isSafe;
        }
      } else {
        InterpretListEnsures(Evaluator(r, s), args);
      }
    }

    lemma RecordSafe(r: Request, s: EntityStore, es: seq<(Attr,Expr)>, rt: RecordType)
      // every entry has some type
      requires forall ae :: ae in es ==> exists t :: IsSafe(r,s,ae.1,t)
      // and the last instance of every required key is safe at the correct type.
      requires forall k :: k in rt ==> KeyExists(k,es) && IsSafe(r,s,LastOfKey(k,es),rt[k].ty)
      ensures IsSafe(r,s,Expr.Record(es),Type.Record(rt))
    {
      if Evaluator(r,s).interpretRecord(es).Ok? {
        InterpretRecordLemmaOk(es,r,s);
      } else {
        InterpretRecordLemmaErr(es,r,s);
      }
    }

    lemma ObjectProjSafeRequired(r: Request, s: EntityStore, e: Expr, t: Type, l: Attr, t': AttrType)
      requires IsSafe(r,s,e,t)
      requires t'.isRequired
      requires SemanticSubty(t,Type.Record(map[l := t']))
      ensures IsSafe(r,s,GetAttr(e,l),t'.ty)
    {}

    lemma ObjectProjSafeGetAttrSafe(r: Request, s: EntityStore, e: Expr, t: Type, l: Attr, t': AttrType)
      requires IsSafe(r,s,e,t)
      requires SemanticSubty(t,Type.Record(map[l := t']))
      requires GetAttrSafe(r,s,e,l)
      ensures IsSafe(r,s,GetAttr(e,l),t'.ty)
    {}

    lemma EntityProjSafe(r: Request, s: EntityStore, e: Expr, l: Attr, lub: EntityLUB, t': Type, isRequired: bool)
      requires IsSafe(r,s,e,Type.Entity(lub))
      requires EntityProjStoreCondition(s, l, lub, t', isRequired)
      requires isRequired || GetAttrSafe(r,s,e,l)
      ensures IsSafe(r,s,GetAttr(e,l),t')
    {}

    lemma RecordHasRequiredTrueSafe(r: Request, s: EntityStore, e: Expr, l: Attr, t: AttrType)
      requires IsSafe(r,s,e,Type.Record(map[l := t]))
      requires t.isRequired
      ensures IsTrue(r,s,HasAttr(e,l))
    {}

    lemma RecordHasOpenRecSafe(r: Request, s: EntityStore, e: Expr, l: Attr)
      requires IsSafe(r,s,e,Type.Record(map[]))
      ensures IsSafe(r,s,HasAttr(e,l),Type.Bool(AnyBool))
    {}

    lemma EntityHasImpossibleFalseSafe(r: Request, s: EntityStore, e: Expr, l: Attr, lub: EntityLUB)
      requires IsSafe(r,s,e,Type.Entity(lub))
      requires forall ev: EntityUID | ExistingEntityInLub(s, ev, lub) ::
                 l !in s.entities[ev].attrs
      ensures IsFalse(r,s,HasAttr(e,l))
    {}

    lemma EntityHasOpenSafe(r: Request, s: EntityStore, e: Expr, l: Attr)
      requires IsSafe(r,s,e,Type.Entity(AnyEntity))
      ensures IsSafe(r,s,HasAttr(e,l),Type.Bool(AnyBool))
    {}

    lemma InSingleSafe(r: Request, s: EntityStore, e1: Expr, e2: Expr)
      requires IsSafe(r,s,e1,Type.Entity(AnyEntity))
      requires IsSafe(r,s,e2,Type.Entity(AnyEntity))
      ensures IsSafe(r,s,BinaryApp(BinaryOp.In,e1,e2),Type.Bool(AnyBool))
    {}

    lemma EntityInEntityMatchesEngine(r: Request, s: EntityStore, u1: EntityUID, u2: EntityUID)
      ensures EntityInEntity(s,u1,u2) == Evaluator(r,s).entityInEntity(u1,u2)
    {}

    lemma InSingleFalseLiterals(r: Request, s: EntityStore, u1: EntityUID, u2: EntityUID)
      requires !EntityInEntity(s,u1,u2)
      ensures IsFalse(r,s,BinaryApp(BinaryOp.In,PrimitiveLit(Primitive.EntityUID(u1)),PrimitiveLit(Primitive.EntityUID(u2))))
    {
      var evaluator := Evaluator(r,s);
      calc == {
        evaluator.interpret(BinaryApp(BinaryOp.In,PrimitiveLit(Primitive.EntityUID(u1)),PrimitiveLit(Primitive.EntityUID(u2))));
        evaluator.applyBinaryOp(BinaryOp.In,Value.EntityUID(u1),Value.EntityUID(u2));
        base.Ok(Value.Bool(evaluator.entityInEntity(u1, u2)));
      }
    }

    lemma InSingleFalseEntityTypeAndLiteral(r: Request, s: EntityStore, e1: Expr, et1: EntityType, u2: EntityUID)
      requires IsSafe(r,s,e1,Type.Entity(EntityLUB({et1})))
      requires forall u1: EntityUID | u1.ty == et1 :: !EntityInEntity(s,u1,u2)
      ensures IsFalse(r,s,BinaryApp(BinaryOp.In,e1,PrimitiveLit(Primitive.EntityUID(u2))))
    {
      var evaluator := Evaluator(r,s);
      var r1 := evaluator.interpret(e1);
      if r1.Ok? {
        var u1 :- assert Value.asEntity(r1.value);
        assert u1.ty == et1;
        assert !EntityInEntity(s,u1,u2);
        assert evaluator.interpret(BinaryApp(BinaryOp.In,e1,PrimitiveLit(Primitive.EntityUID(u2)))) == base.Ok(Value.FALSE);
      }
    }

    lemma InSingleFalseTypes(r: Request, s: EntityStore, e1: Expr, e2: Expr, t1: Type, t2: Type)
      requires subty(t1,Type.Entity(AnyEntity))
      requires subty(t2,Type.Entity(AnyEntity))
      requires IsSafe(r,s,e1,t1)
      requires IsSafe(r,s,e2,t2)
      requires forall u1, u2: EntityUID |
                 InstanceOfType(Value.EntityUID(u1), t1) && InstanceOfType(Value.EntityUID(u2), t2) ::
                 !EntityInEntity(s,u1,u2)
      ensures IsFalse(r,s,BinaryApp(BinaryOp.In,e1,e2))
    {
      var evaluator := Evaluator(r,s);
      if evaluator.interpret(BinaryApp(BinaryOp.In,e1,e2)).Ok? {
        var u1 := Value.asEntity(evaluator.interpret(e1).value).value;
        var u2 := Value.asEntity(evaluator.interpret(e2).value).value;
        assert !EntityInEntity(s,u1,u2);
      }
    }

    lemma InSetSafe(r: Request, s: EntityStore, e1: Expr, e2: Expr)
      requires IsSafe(r,s,e1,Type.Entity(AnyEntity))
      requires IsSafe(r,s,e2,Type.Set(Type.Entity(AnyEntity)))
      ensures IsSafe(r,s,BinaryApp(BinaryOp.In,e1,e2),Type.Bool(AnyBool))
    {}

    lemma InSetFalseIfAllFalse(r: Request, s: EntityStore, e1: Expr, e2s: seq<Expr>)
      requires IsSafe(r,s,e1,Type.Entity(AnyEntity))
      requires forall i | 0 <= i < |e2s| ::
                 IsSafe(r,s,e2s[i],Type.Entity(AnyEntity)) &&
                 IsFalse(r,s,BinaryApp(BinaryOp.In,e1,e2s[i]))
      ensures IsFalse(r,s,BinaryApp(BinaryOp.In,e1,Expr.Set(e2s)))
    {
      InterpretSetLemma(e2s,r,s);
      var evaluator := Evaluator(r,s);
      var res := evaluator.interpret(BinaryApp(BinaryOp.In,e1,Expr.Set(e2s)));
      var r1 := evaluator.interpret(e1);
      var r2 := evaluator.interpret(Expr.Set(e2s));
    }

    lemma InSetFalseTypes(r: Request, s: EntityStore, e1: Expr, e2: Expr, t1: Type, t2: Type)
      requires subty(t1,Type.Entity(AnyEntity))
      requires subty(t2,Type.Entity(AnyEntity))
      requires IsSafe(r,s,e1,t1)
      requires IsSafe(r,s,e2,Type.Set(t2))
      requires forall u1, u2: EntityUID |
                 InstanceOfType(Value.EntityUID(u1), t1) && InstanceOfType(Value.EntityUID(u2), t2) ::
                 !EntityInEntity(s,u1,u2)
      ensures IsFalse(r,s,BinaryApp(BinaryOp.In,e1,e2))
    {
      var evaluator := Evaluator(r,s);
      var r1 := evaluator.interpret(e1);
      var r2 := evaluator.interpret(e2);
      if r1.Ok? && r2.Ok? {
        var u1 := Value.asEntity(r1.value).value;
        var s2 := Value.asSet(r2.value).value;
        assert forall us2 <- s2 :: InstanceOfType(us2,t2);
        var us2 :- assert evaluator.checkEntitySet(s2);
        assert forall u2 <- us2 :: !EntityInEntity(s,u1,u2);
      }
    }
  }
}
