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
include "model.dfy"
include "base.dfy"

// This module contains the core type soundness proof. Rather than importing
// the definitional evaluator, it relies on the abstract model.
// The final lemma is `SoundToplevel`, at the bottom of the file.
module validation.thm.soundness {
  import opened def
  import opened def.core
  import opened types
  import opened subtyping
  import opened typechecker
  import opened model
  import opened base
  import opened ext

  type Result<T> = types.Result<T>

  // A value of type SemanticSoundnessProof(reqty,ets,acts,q,s) contains a
  // proof (`lemma SoundToplevel` at the bottom of the file) that any
  // expression `e` typed in context (reqty, ets, acts) and evaluated under (r,s)
  // is safe according to the model, assuming the context assigns correct
  // types to the fields in query `q`, and the entities in store `s`.
  //
  // The proofs in this file are robust to changes in the evaluator, since they
  // only depend on the abstract `model`.
  datatype SemanticSoundnessProof = SSP(
    reqty: RequestType,
    ets: EntityTypeStore,
    acts: ActionStore,
    r: Request,
    s: EntityStore)
  {

    ghost predicate WellTyped(e: Expr, effs: Effects)
    {
      Typechecker(ets,acts,reqty).infer(e,effs).Ok?
    }

    function getType(e: Expr, effs: Effects): Type
      requires WellTyped(e,effs)
    {
      Typechecker(ets,acts,reqty).infer(e,effs).value.0
    }

    function getEffects(e: Expr, effs: Effects): Effects
      requires WellTyped(e,effs)
    {
      Typechecker(ets,acts,reqty).infer(e,effs).value.1
    }

    ghost predicate Typesafe(e: Expr, effs: Effects, t: Type)
    {
      WellTyped(e,effs) && subty(getType(e, effs), t)
    }

    // On input to the typechecking function, for any (e,k) in the Effects,
    // e is a record- or entity-typed expression that has key k.
    ghost predicate {:opaque} EffectsInvariant (effs: Effects) {
      forall e, k | (e, k) in effs.effs :: GetAttrSafe(r,s,e,k)
    }

    // The Effects output by the typechecking function, will satisfy
    // `EffectsInvariant` provided that the input expression is true.
    ghost predicate GuardedEffectsInvariant (e: Expr, effs: Effects)
    {
      IsTrueStrong(r,s,e) ==> EffectsInvariant(effs)
    }

    lemma EmptyEffectsInvariant ()
      ensures EffectsInvariant(Effects.empty())
    {
      reveal EffectsInvariant();
    }

    lemma SoundLit(p: Primitive, t: Type, effs: Effects)
      decreases PrimitiveLit(p) , 0
      requires Typesafe(PrimitiveLit(p),effs,t)
      ensures IsSafe(r,s,PrimitiveLit(p),t)
      ensures getEffects(PrimitiveLit(p),effs) == Effects.empty()
    {
      assert InstanceOfType(Primitive(p),typeOfPrim(p)) by {
        PrimSafeAtInferredType(p);
      }

      assert SemanticSubty(typeOfPrim(p),t) by {
        SubtyCompat(typeOfPrim(p),t);
      }

      assert InstanceOfType(Primitive(p),t) by {
        SemSubtyTransportVal(typeOfPrim(p),t,Primitive(p));
      }

      assert IsSafe(r,s,PrimitiveLit(p),t) by{
        PrimSafeLift(r,s,p,t);
      }
    }

    lemma SoundVar(x: Var, t: Type, effs: Effects)
      decreases Var(x) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires Typesafe(Var(x),effs,t)
      ensures IsSafe(r,s,Var(x),t)
      ensures getEffects(Var(x),effs) == Effects.empty()
    {
      var t' :| getType(Var(x),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferVar(x) == types.Ok(t');
      match x {
        case Principal =>
          assert IsSafe(r,s,Var(Principal),t') by { PrincipalIsSafe(r,s,t'); }
          assert IsSafe(r,s,Var(Principal),t) by {
            SubtyCompat(t',t);
            SemSubtyTransport(r,s,Var(Principal),t',t);
          }
        case Action =>
          assert IsSafe(r,s,Var(Action),t') by { ActionIsSafe(r,s,t'); }
          assert IsSafe(r,s,Var(Action),t) by {
            SubtyCompat(t',t);
            SemSubtyTransport(r,s,Var(Action),t',t);
          }
        case Resource =>
          assert IsSafe(r,s,Var(Resource),t') by { ResourceIsSafe(r,s,t'); }
          assert IsSafe(r,s,Var(Resource),t) by {
            SubtyCompat(t',t);
            SemSubtyTransport(r,s,Var(Resource),t',t);
          }
        case Context =>
          assert IsSafe(r,s,Var(Context),Type.Record(reqty.context)) by {
            ContextIsSafe(r,s,Type.Record(reqty.context));
          }
          assert IsSafe(r,s,Var(Context),t) by {
            SubtyCompat(Type.Record(reqty.context),t);
            SemSubtyTransport(r,s,Var(Context),Type.Record(reqty.context),t);
          }
      }
    }

    lemma EffectsInvariantUnion(effs1: Effects, effs2: Effects)
      requires EffectsInvariant(effs1)
      requires EffectsInvariant(effs2)
      ensures EffectsInvariant(effs1.union(effs2))
    {
      reveal EffectsInvariant();
    }

    lemma EffectsInvariantIntersectL(effs1: Effects, effs2: Effects)
      requires EffectsInvariant(effs1)
      ensures EffectsInvariant(effs1.intersect(effs2))
    {
      assert effs1.intersect(effs2) == effs2.intersect(effs1) by {
        reveal EffectsInvariant();
      }
      EffectsInvariantIntersectR(effs2,effs1);
    }

    lemma EffectsInvariantIntersectR(effs1: Effects, effs2: Effects)
      requires EffectsInvariant(effs2)
      ensures EffectsInvariant(effs1.intersect(effs2))
    {
      reveal EffectsInvariant();
    }

    lemma SoundIf(e: Expr, e1: Expr, e2: Expr, t: Type, effs: Effects)
      decreases If(e,e1,e2) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(If(e,e1,e2),effs,t)
      ensures IsSafe(r,s,If(e,e1,e2),t)
      ensures GuardedEffectsInvariant(If(e,e1,e2),getEffects(If(e,e1,e2),effs))
    {
      var t' :| getType(If(e,e1,e2),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferIf(e,e1,e2,effs).Ok?;
      var (bt, effs1) := Typechecker(ets,acts,reqty).inferBoolType(e,effs).value;
      assert IsSafe(r,s,e,Type.Bool(bt)) && GuardedEffectsInvariant(e,effs1) by {
        assert getType(e,effs) == Type.Bool(bt);
        assert subty(Type.Bool(bt),Type.Bool(bt));
        assert Typesafe(e,effs,Type.Bool(bt));
        Sound(e,Type.Bool(bt),effs);
      }
      match bt {
        case True =>
          assert IsTrue(r,s,e);
          var (t1,effs2) := Typechecker(ets,acts,reqty).infer(e1,effs.union(effs1)).value;
          assert Typesafe(e1,effs.union(effs1),t1) by { SubtyRefl(t1); }
          if IsTrueStrong(r,s,e) {
            assert EffectsInvariant(effs1);
            assert IsSafe(r,s,e1,t1) && GuardedEffectsInvariant(e1,effs2) by {
              EffectsInvariantUnion(effs,effs1);
              Sound(e1,t1,effs.union(effs1));
            }
            assert IsSafe(r,s,If(e,e1,e2),t') by { IteTrueSafe(r,s,e,e1,e2,t'); }
            assert IsSafe(r,s,If(e,e1,e2),t) by {
              SubtyCompat(t',t);
              SemSubtyTransport(r,s,If(e,e1,e2),t',t);
            }
            assert GuardedEffectsInvariant(If(e,e1,e2),effs1.union(effs2)) by {
              if IsTrueStrong(r,s,If(e,e1,e2)) {
                IteTrueStrongTrue(r,s,e,e1,e2);
                assert EffectsInvariant(effs2);
                EffectsInvariantUnion(effs1,effs2);
              }
            }
          } else {
            assert IsSafe(r,s,If(e,e1,e2),t) by {
              IteError(r,s,e,e1,e2,Type.Bool(True),t);
            }
            assert GuardedEffectsInvariant(If(e,e1,e2),effs1.union(effs2)) by {
              IteError(r,s,e,e1,e2,Type.Bool(True),Type.Bool(True));
              assert !IsTrueStrong(r,s,If(e,e1,e2));
            }
          }
        case False =>
          assert IsFalse(r,s,e);
          var (t2,effs2) := Typechecker(ets,acts,reqty).infer(e2,effs).value;
          assert Typesafe(e2,effs,t2) by { SubtyRefl(t2); }
          assert IsSafe(r,s,e2,t2) && GuardedEffectsInvariant(e2,effs2) by {
            Sound(e2,t2,effs);
          }
          assert IsSafe(r,s,If(e,e1,e2),t') by { IteFalseSafe(r,s,e,e1,e2,t'); }
          assert IsSafe(r,s,If(e,e1,e2),t) by {
            SubtyCompat(t',t);
            SemSubtyTransport(r,s,If(e,e1,e2),t',t);
          }
          assert GuardedEffectsInvariant(If(e,e1,e2),effs2) by {
            if IsTrueStrong(r,s,If(e,e1,e2)) {
              IteTrueStrongFalse(r,s,e,e1,e2);
              assert EffectsInvariant(effs2);
            }
          }
        case AnyBool =>
          var (t1,effs2) := Typechecker(ets,acts,reqty).infer(e1,effs.union(effs1)).value;
          var (t2,effs3) := Typechecker(ets,acts,reqty).infer(e2,effs).value;
          assert Typesafe(e1,effs.union(effs1),t1) by { SubtyRefl(t1); }
          assert Typesafe(e2,effs,t2) by { SubtyRefl(t2); }
          assert t' == lubOpt(t1,t2).value;
          assert subty(t1,t') && subty(t2,t') by { LubIsUB(t1,t2,t'); }
          if IsSafeStrong(r,s,e,Type.Bool(bt)) {
            if IsTrue(r,s,e) {
              // `e` evaluates to true
              IsTrueImpliesIsTrueStrong(r,s,e,Type.Bool(bt));
              assert IsTrueStrong(r,s,e);
              assert EffectsInvariant(effs1);
              assert IsSafe(r,s,e1,t1) && GuardedEffectsInvariant(e1,effs2) by {
                EffectsInvariantUnion(effs,effs1);
                Sound(e1,t1,effs.union(effs1));
              }
              assert IsSafe(r,s,If(e,e1,e2),t1) by { IteTrueSafe(r,s,e,e1,e2,t1); }
              assert IsSafe(r,s,If(e,e1,e2),t) by {
                SubtyCompat(t1,t');
                SubtyCompat(t',t);
                SemSubtyTransport(r,s,If(e,e1,e2),t1,t);
              }
              assert GuardedEffectsInvariant(If(e,e1,e2),effs1.union(effs2)) by {
                if IsTrueStrong(r,s,If(e,e1,e2)) {
                  IteTrueStrongTrue(r,s,e,e1,e2);
                  EffectsInvariantUnion(effs1,effs2);
                }
              }
              assert GuardedEffectsInvariant(If(e,e1,e2),effs1.union(effs2).intersect(effs3)) by {
                if IsTrueStrong(r,s,If(e,e1,e2)) {
                  EffectsInvariantIntersectL(effs1.union(effs2),effs3);
                }
              }
            } else {
              // `e` evaluates to false
              NotTrueImpliesFalse(r,s,e,bt);
              assert IsFalse(r,s,e);
              assert IsSafe(r,s,e2,t2) && GuardedEffectsInvariant(e2,effs3) by {
                Sound(e2,t2,effs);
              }
              assert IsSafe(r,s,If(e,e1,e2),t2) by { IteFalseSafe(r,s,e,e1,e2,t2); }
              assert IsSafe(r,s,If(e,e1,e2),t) by {
                SubtyCompat(t2,t');
                SubtyCompat(t',t);
                SemSubtyTransport(r,s,If(e,e1,e2),t2,t);
              }
              assert GuardedEffectsInvariant(If(e,e1,e2),effs3) by {
                if IsTrueStrong(r,s,If(e,e1,e2)) {
                  IteTrueStrongFalse(r,s,e,e1,e2);
                }
              }
              assert GuardedEffectsInvariant(If(e,e1,e2),effs1.union(effs2).intersect(effs3)) by {
                if IsTrueStrong(r,s,If(e,e1,e2)) {
                  EffectsInvariantIntersectR(effs1.union(effs2),effs3);
                }
              }
            }
          } else {
            // `e` produces an error
            assert IsSafe(r,s,If(e,e1,e2),t) by {
              IteError(r,s,e,e1,e2,Type.Bool(bt),t);
            }
            assert GuardedEffectsInvariant(If(e,e1,e2),effs1.union(effs2).intersect(effs3)) by {
              IteError(r,s,e,e1,e2,Type.Bool(bt),Type.Bool(True));
              assert !IsTrueStrong(r,s,If(e,e1,e2));
            }
          }
      }
    }

    lemma SoundAnd(e1: Expr, e2: Expr, t: Type, effs: Effects)
      decreases And(e1,e2) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(And(e1,e2),effs,t)
      ensures IsSafe(r,s,And(e1,e2),t)
      ensures GuardedEffectsInvariant(And(e1,e2),getEffects(And(e1,e2),effs))
    {
      var t' :| getType(And(e1,e2),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferAnd(e1,e2,effs).Ok?;
      var (bt1, effs1) := Typechecker(ets,acts,reqty).inferBoolType(e1,effs).value;
      assert Typesafe(e1,effs,Type.Bool(bt1));
      assert IsSafe(r,s,e1,Type.Bool(bt1)) && GuardedEffectsInvariant(e1,effs1) by {
        Sound(e1,Type.Bool(bt1),effs);
      }
      assert GuardedEffectsInvariant(And(e1,e2),Effects.empty()) by {
        EmptyEffectsInvariant();
      }
      match bt1 {
        case False =>
          assert IsSafe(r,s,And(e1,e2),t') by { AndLShortSafe(r,s,e1,e2); }
          assert IsSafe(r,s,And(e1,e2),t) by {
            SubtyCompat(t',t);
            SemSubtyTransport(r,s,And(e1,e2),t',t);
          }
        case _ =>
          var res := Typechecker(ets,acts,reqty).inferBoolType(e2,effs.union(effs1)).value;
          var bt2 := res.0;
          var effs2 := res.1;
          assert Typesafe(e2,effs.union(effs1),Type.Bool(bt2));
          if IsSafeStrong(r,s,e1,Type.Bool(bt1)) {
            if IsTrue(r,s,e1) {
              // `e1` evaluates to true
              IsTrueImpliesIsTrueStrong(r,s,e1,Type.Bool(bt1));
              assert IsTrueStrong(r,s,e1);
              assert EffectsInvariant(effs1);
              assert IsSafe(r,s,e2,Type.Bool(bt2)) && GuardedEffectsInvariant(e2,effs2) by {
                EffectsInvariantUnion(effs,effs1);
                Sound(e2,Type.Bool(bt2),effs.union(effs1));
              }
              match bt2 {
                case False =>
                  assert IsFalse(r,s,e2);
                  assert IsSafe(r,s,e1,Type.Bool(AnyBool)) by {
                    assert subty(Type.Bool(bt1),Type.Bool(AnyBool));
                    SubtyCompat(Type.Bool(bt1),Type.Bool(AnyBool));
                    SemSubtyTransport(r,s,e1,Type.Bool(bt1),Type.Bool(AnyBool));
                  }
                  assert IsSafe(r,s,And(e1,e2),t') by {
                    AndRShortSafe(r,s,e1,e2);
                  }
                  assert IsSafe(r,s,And(e1,e2),t) by {
                    SubtyCompat(t',t);
                    SemSubtyTransport(r,s,And(e1,e2),t',t);
                  }
                case True =>
                  assert IsTrue(r,s,e2);
                  assert SemanticSubty(Type.Bool(bt1),Type.Bool(AnyBool)) by {
                    assert subty(Type.Bool(bt1),Type.Bool(AnyBool));
                    SubtyCompat(Type.Bool(bt1),Type.Bool(AnyBool));
                  }
                  assert IsSafe(r,s,And(e1,e2),Type.Bool(bt1)) by {
                    AndLRetSafe(r,s,e1,e2,Type.Bool(bt1));
                  }
                  assert IsSafe(r,s,And(e1,e2),t) by {
                    SubtyCompat(t',t);
                    SemSubtyTransport(r,s,And(e1,e2),t',t);
                  }
                  assert GuardedEffectsInvariant(And(e1,e2),effs1.union(effs2)) by {
                    if IsTrueStrong(r,s,And(e1,e2)) {
                      AndTrueStrong(r,s,e1,e2);
                      assert EffectsInvariant(effs2);
                      EffectsInvariantUnion(effs1,effs2);
                    }
                  }
                case _ =>
                  assert IsSafe(r,s,e1,Type.Bool(AnyBool)) by {
                    SubtyCompat(Type.Bool(bt1),Type.Bool(AnyBool));
                    SemSubtyTransport(r,s,e1,Type.Bool(bt1),Type.Bool(AnyBool));
                  }
                  assert IsSafe(r,s,e2,Type.Bool(AnyBool)) by {
                    SubtyCompat(Type.Bool(bt2),Type.Bool(AnyBool));
                    SemSubtyTransport(r,s,e2,Type.Bool(bt2),Type.Bool(AnyBool));
                  }
                  assert IsSafe(r,s,And(e1,e2),Type.Bool(AnyBool)) by { AndSafe(r,s,e1,e2); }
                  assert IsSafe(r,s,And(e1,e2),t) by {
                    SubtyCompat(t',t);
                    SemSubtyTransport(r,s,And(e1,e2),t',t);
                  }
                  assert GuardedEffectsInvariant(And(e1,e2),effs1.union(effs2)) by {
                    if IsTrueStrong(r,s,And(e1,e2)) {
                      AndTrueStrong(r,s,e1,e2);
                      assert EffectsInvariant(effs2);
                      EffectsInvariantUnion(effs1,effs2);
                    }
                  }
              }
            } else {
              // `e1` evaluates to false
              NotTrueImpliesFalse(r,s,e1,bt1);
              assert IsFalse(r,s,e1);
              assert IsFalse(r,s,And(e1,e2)) by { AndLShortSafe(r,s,e1,e2); }
              assert IsSafe(r,s,And(e1,e2),t) by {
                SubtyCompat(Type.Bool(False),t);
                SemSubtyTransport(r,s,And(e1,e2),Type.Bool(False),t);
              }
              match bt2 {
                case False =>
                case True =>
                  assert GuardedEffectsInvariant(And(e1,e2),effs1.union(effs2)) by {
                    assert IsFalse(r,s,And(e1,e2));
                    FalseImpliesNotTrueStrong(r,s,And(e1,e2));
                    assert !IsTrueStrong(r,s,And(e1,e2));
                  }
                case AnyBool =>
                  assert GuardedEffectsInvariant(And(e1,e2),effs1.union(effs2)) by {
                    assert IsFalse(r,s,And(e1,e2));
                    FalseImpliesNotTrueStrong(r,s,And(e1,e2));
                    assert !IsTrueStrong(r,s,And(e1,e2));
                  }
              }
            }
          } else {
            // `e1` produces an error
            assert IsSafe(r,s,And(e1,e2),t) by {
              AndError(r,s,e1,e2,Type.Bool(bt1),t);
            }
            assert GuardedEffectsInvariant(And(e1,e2),effs1.union(effs2)) by {
              AndError(r,s,e1,e2,Type.Bool(bt1),Type.Bool(True));
              assert !IsTrueStrong(r,s,And(e1,e2));
            }
          }
      }
    }

    lemma SoundOr(e1: Expr, e2: Expr, t: Type, effs: Effects)
      decreases Or(e1,e2) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(Or(e1,e2),effs,t)
      ensures IsSafe(r,s,Or(e1,e2),t)
      ensures GuardedEffectsInvariant(Or(e1,e2),getEffects(Or(e1,e2),effs))
    {
      var t' :| getType(Or(e1,e2),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferOr(e1,e2,effs).Ok?;
      var (bt1, effs1) := Typechecker(ets,acts,reqty).inferBoolType(e1,effs).value;
      assert Typesafe(e1,effs,Type.Bool(bt1));
      assert IsSafe(r,s,e1,Type.Bool(bt1)) && GuardedEffectsInvariant(e1,effs1) by {
        Sound(e1,Type.Bool(bt1),effs);
      }
      assert GuardedEffectsInvariant(Or(e1,e2),Effects.empty()) by {
        EmptyEffectsInvariant();
      }
      match bt1 {
        case True =>
          assert IsTrue(r,s,e1);
          assert IsSafe(r,s,Or(e1,e2),t') by { OrLShortSafe(r,s,e1,e2); }
          assert IsSafe(r,s,Or(e1,e2),t) by {
            SubtyCompat(t',t);
            SemSubtyTransport(r,s,Or(e1,e2),t',t);
          }
        case False =>
          assert IsFalse(r,s,e1);
          var (bt2, effs2) := Typechecker(ets,acts,reqty).inferBoolType(e2,effs).value;
          assert Typesafe(e2,effs,Type.Bool(bt2));
          assert IsSafe(r,s,e2,Type.Bool(bt2)) && GuardedEffectsInvariant(e2,effs2) by {
            Sound(e2,Type.Bool(bt2),effs);
          }
          assert SemanticSubty(Type.Bool(bt2),Type.Bool(AnyBool)) by {
            assert subty(Type.Bool(bt2),Type.Bool(AnyBool));
            SubtyCompat(Type.Bool(bt2),Type.Bool(AnyBool));
          }
          assert IsSafe(r,s,Or(e1,e2),Type.Bool(bt2)) by { OrRRetSafe(r,s,e1,e2,Type.Bool(bt2)); }
          assert IsSafe(r,s,Or(e1,e2),t) by {
            SubtyCompat(t',t);
            SemSubtyTransport(r,s,Or(e1,e2),t',t);
          }
          assert GuardedEffectsInvariant(Or(e1,e2),effs2) by {
            if IsTrueStrong(r,s,Or(e1,e2)) {
              OrTrueStrong(r,s,e1,e2);
              FalseImpliesNotTrueStrong(r,s,e1);
              assert IsTrueStrong(r,s,e2);
              assert EffectsInvariant(effs2);
            }
          }
        case _ =>
          var (bt2, effs2) := Typechecker(ets,acts,reqty).inferBoolType(e2,effs).value;
          assert Typesafe(e2,effs,Type.Bool(bt2));
          assert IsSafe(r,s,e2,Type.Bool(bt2)) && GuardedEffectsInvariant(e2,effs2) by {
            Sound(e2,Type.Bool(bt2),effs);
          }
          match bt2 {
            case True =>
              assert IsTrue(r,s,e2);
              assert IsSafe(r,s,e1,Type.Bool(AnyBool)) by {
                SubtyCompat(Type.Bool(bt1),Type.Bool(AnyBool));
                SemSubtyTransport(r,s,e1,Type.Bool(bt1),Type.Bool(AnyBool));
              }
              assert IsTrue(r,s,Or(e1,e2)) by { OrRShortSafe(r,s,e1,e2); }
              assert IsSafe(r,s,Or(e1,e2),t) by {
                SubtyCompat(Type.Bool(True),t);
                SemSubtyTransport(r,s,Or(e1,e2),Type.Bool(True),t);
              }
            case False =>
              assert IsFalse(r,s,e2);
              assert IsSafe(r,s,Or(e1,e2),t) by {
                OrLRetSafe(r,s,e1,e2,Type.Bool(bt1));
                SubtyCompat(Type.Bool(bt1),t);
                SemSubtyTransport(r,s,Or(e1,e2),Type.Bool(bt1),t);
              }
              assert GuardedEffectsInvariant(Or(e1,e2),effs1) by {
                if IsTrueStrong(r,s,Or(e1,e2)) {
                  OrTrueStrong(r,s,e1,e2);
                  FalseImpliesNotTrueStrong(r,s,e2);
                  assert IsTrueStrong(r,s,e1);
                  assert EffectsInvariant(effs1);
                }
              }
            case _ =>
              assert IsSafe(r,s,e1,Type.Bool(AnyBool)) by {
                SubtyCompat(Type.Bool(bt1),Type.Bool(AnyBool));
                SemSubtyTransport(r,s,e1,Type.Bool(bt1),Type.Bool(AnyBool));
              }
              assert IsSafe(r,s,e2,Type.Bool(AnyBool)) by {
                SubtyCompat(Type.Bool(bt2),Type.Bool(AnyBool));
                SemSubtyTransport(r,s,e2,Type.Bool(bt2),Type.Bool(AnyBool));
              }
              assert IsSafe(r,s,Or(e1,e2),Type.Bool(AnyBool)) by { OrSafe(r,s,e1,e2); }
              assert IsSafe(r,s,Or(e1,e2),t) by {
                SubtyCompat(t',t);
                SemSubtyTransport(r,s,Or(e1,e2),t',t);
              }
              assert GuardedEffectsInvariant(Or(e1,e2),effs1.intersect(effs2)) by {
                if IsTrueStrong(r,s,Or(e1,e2)) {
                  OrTrueStrong(r,s,e1,e2);
                  if IsTrueStrong(r,s,e1) {
                    assert EffectsInvariant(effs1);
                    EffectsInvariantIntersectL(effs1,effs2);
                  } else {
                    assert IsTrueStrong(r,s,e2);
                    assert EffectsInvariant(effs2);
                    EffectsInvariantIntersectR(effs1,effs2);
                  }
                }
              }
          }
      }
    }

    lemma SoundNot(e: Expr, t: Type, effs: Effects)
      decreases UnaryApp(Not,e) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(UnaryApp(Not,e),effs,t)
      ensures IsSafe(r,s,UnaryApp(Not,e),t)
      ensures getEffects(UnaryApp(Not,e),effs) == Effects.empty()
    {
      var t' :| getType(UnaryApp(Not,e),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferNot(e,effs).Ok?;
      var (bt,_) := Typechecker(ets,acts,reqty).inferBoolType(e,effs).value;
      assert t' == Type.Bool(bt.not());
      assert Typesafe(e,effs,Type.Bool(bt)) by { SubtyRefl(Type.Bool(bt)); }
      assert IsSafe(r,s,e,Type.Bool(bt)) by { Sound(e,Type.Bool(bt),effs); }
      assert IsSafe(r,s,UnaryApp(Not,e),t') by {
        match bt {
          case AnyBool => NotSafe(r,s,e);
          case True => NotTrueSafe(r,s,e);
          case False => NotFalseSafe(r,s,e);
        }
      }
      assert IsSafe(r,s,UnaryApp(Not,e),t) by {
        SubtyCompat(t',t);
        SemSubtyTransport(r,s,UnaryApp(Not,e),t',t);
      }
    }

    lemma SoundNeg(e: Expr, t: Type, effs: Effects)
      decreases UnaryApp(Neg,e) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(UnaryApp(Neg,e),effs,t)
      ensures IsSafe(r,s,UnaryApp(Neg,e),t)
      ensures getEffects(UnaryApp(Neg,e),effs) == Effects.empty()
    {
      var t' :| getType(UnaryApp(Neg,e),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferArith1(Neg,e,effs) == types.Ok(Type.Int);
      assert Typechecker(ets,acts,reqty).ensureIntType(e,effs).Ok?;
      assert Typesafe(e,effs,Type.Int);
      assert IsSafe(r,s,e,Type.Int) by { Sound(e,Type.Int,effs); }
      assert IsSafe(r,s,UnaryApp(Neg,e),t') by { NegSafe(r,s,e); }
      assert IsSafe(r,s,UnaryApp(Neg,e),t) by {
        SubtyCompat(t',t);
        SemSubtyTransport(r,s,UnaryApp(Neg,e),t',t);
      }
    }

    lemma SoundMulBy(i: int, e: Expr, t: Type, effs: Effects)
      decreases UnaryApp(MulBy(i),e) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(UnaryApp(MulBy(i),e),effs,t)
      ensures IsSafe(r,s,UnaryApp(MulBy(i),e),t)
      ensures getEffects(UnaryApp(MulBy(i),e),effs) == Effects.empty()
    {
      var t' :| getType(UnaryApp(MulBy(i),e),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferArith1(MulBy(i),e,effs) == types.Ok(Type.Int);
      assert Typechecker(ets,acts,reqty).ensureIntType(e,effs).Ok?;
      assert Typesafe(e,effs,Type.Int);
      assert IsSafe(r,s,e,Type.Int) by { Sound(e,Type.Int,effs); }
      assert IsSafe(r,s,UnaryApp(MulBy(i),e),t') by { MulBySafe(r,s,e,i); }
      assert IsSafe(r,s,UnaryApp(MulBy(i),e),t) by {
        SubtyCompat(t',t);
        SemSubtyTransport(r,s,UnaryApp(MulBy(i),e),t',t);
      }
    }

    lemma SoundLike(e: Expr, p: Pattern, t: Type, effs: Effects)
      decreases UnaryApp(Like(p),e) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(UnaryApp(Like(p),e),effs,t)
      ensures IsSafe(r,s,UnaryApp(Like(p),e),t)
      ensures getEffects(UnaryApp(Like(p),e),effs) == Effects.empty()
    {
      var t' :| getType(UnaryApp(Like(p),e),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferLike(p,e,effs) == types.Ok(Type.Bool(AnyBool));
      assert Typechecker(ets,acts,reqty).ensureStringType(e,effs).Ok?;
      assert Typesafe(e,effs,Type.String);
      assert IsSafe(r,s,e,Type.String) by { Sound(e,Type.String,effs); }
      assert IsSafe(r,s,UnaryApp(Like(p),e),t') by { LikeSafe(r,s,e,p); }
      assert IsSafe(r,s,UnaryApp(Like(p),e),t) by {
        SubtyCompat(t',t);
        SemSubtyTransport(r,s,UnaryApp(Like(p),e),t',t);
      }
    }

    const unspecifiedEntityType := Type.Entity(EntityLUB({EntityType.UNSPECIFIED}))

    // Take advantage of the fact that in the current implementation, an
    // unspecified entity belongs to unspecifiedEntityType, and we can reuse
    // our logic about LUBs to show that it is different from any "specified"
    // entity. This might not work in the future if we restructure EntityType to
    // have a separate alternative for unspecified entities like in production.
    lemma UnspecifiedVarHasUnspecifiedEntityType(e: Expr)
      requires Typechecker(ets,acts,reqty).isUnspecifiedVar(e)
      requires InstanceOfRequestType(r,reqty)
      ensures IsSafe(r,s,e,unspecifiedEntityType)
    {
      match e {
        case Var(Principal) =>
          assert r.principal == unspecifiedPrincipalEuid;
          PrincipalIsSafe(r,s,unspecifiedEntityType);
        case Var(Resource) =>
          assert r.resource == unspecifiedResourceEuid;
          ResourceIsSafe(r,s,unspecifiedEntityType);
      }
    }

    lemma SoundEqAux(u1: EntityUID, u2: EntityUID, t: Type, effs: Effects)
      requires Typesafe(BinaryApp(BinaryOp.Eq,PrimitiveLit(Primitive.EntityUID(u1)),PrimitiveLit(Primitive.EntityUID(u2))),effs,t)
      ensures IsSafe(r,s,BinaryApp(BinaryOp.Eq,PrimitiveLit(Primitive.EntityUID(u1)),PrimitiveLit(Primitive.EntityUID(u2))),t)
    {
      var e1: Expr := PrimitiveLit(Primitive.EntityUID(u1));
      var e2: Expr := PrimitiveLit(Primitive.EntityUID(u2));
      var t' :| getType(BinaryApp(BinaryOp.Eq,e1,e2),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferEq(e1,e2,effs) == types.Ok(t');
      // Somehow, these unused variables help nudge Dafny to complete the proof.
      var t1 := getType(e1,effs);
      var t2 := getType(e2,effs);
      if u1 == u2 {
        assert t' == Type.Bool(True);
        assert IsSafe(r,s,BinaryApp(BinaryOp.Eq,e1,e2),t') by { EqEntitySameSafe(r,s,u1); }
        assert IsSafe(r,s,BinaryApp(BinaryOp.Eq,e1,e2),t) by {
          SubtyCompat(t',t);
          SemSubtyTransport(r,s,BinaryApp(BinaryOp.Eq,e1,e2),t',t); }
      } else {
        assert t' == Type.Bool(False);
        assert IsSafe(r,s,BinaryApp(BinaryOp.Eq,e1,e2),t') by { EqEntityDiffSafe(r,s,u1,u2); }
        assert IsSafe(r,s,BinaryApp(BinaryOp.Eq,e1,e2),t) by {
          SubtyCompat(t',t);
          SemSubtyTransport(r,s,BinaryApp(BinaryOp.Eq,e1,e2),t',t); }
      }
    }

    lemma SoundEq(e1: Expr, e2: Expr, t: Type, effs: Effects)
      decreases BinaryApp(BinaryOp.Eq,e1,e2) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(BinaryApp(BinaryOp.Eq,e1,e2),effs,t)
      ensures IsSafe(r,s,BinaryApp(BinaryOp.Eq,e1,e2),t)
      ensures getEffects(BinaryApp(BinaryOp.Eq,e1,e2),effs) == Effects.empty()
    {
      var t' :| getType(BinaryApp(BinaryOp.Eq,e1,e2),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferEq(e1,e2,effs) == types.Ok(t');
      var t1 := getType(e1,effs);
      var t2 := getType(e2,effs);
      assert Typesafe(e1,effs,t1) by { SubtyRefl(t1); }
      assert Typesafe(e2,effs,t2) by { SubtyRefl(t2); }
      assert IsSafe(r,s,e1,t1) by { Sound(e1,t1,effs); }
      assert IsSafe(r,s,e2,t2) by { Sound(e2,t2,effs); }
      match (e1,e2,t1,t2) {
        case (PrimitiveLit(EntityUID(u1)),PrimitiveLit(EntityUID(u2)),_,_) =>
          SoundEqAux(u1,u2,t,effs);
        case _ =>
          if t1.Entity? && t2.Entity? && t1.lub.disjoint(t2.lub) {
            assert t' == Type.Bool(False);
            EqFalseIsSafe(r,s,e1,e2,t1.lub,t2.lub);
          } else if Typechecker(ets,acts,reqty).isUnspecifiedVar(e1) && t2.Entity? && t2.lub.specified() {
            assert t' == Type.Bool(False);
            UnspecifiedVarHasUnspecifiedEntityType(e1);
            EqFalseIsSafe(r,s,e1,e2,unspecifiedEntityType.lub,t2.lub);
          } else {
            assert t' == Type.Bool(AnyBool);
            EqIsSafe(r,s,e1,e2,t1,t2);
          }
          assert IsSafe(r,s,BinaryApp(BinaryOp.Eq,e1,e2),t) by {
            SubtyCompat(t',t);
            SemSubtyTransport(r,s,BinaryApp(BinaryOp.Eq,e1,e2),t',t);
          }
      }
    }

    lemma SoundIneq(op: BinaryOp, e1: Expr, e2: Expr, t: Type, effs: Effects)
      decreases BinaryApp(op,e1,e2) , 0
      requires op == Less || op == BinaryOp.LessEq
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(BinaryApp(op,e1,e2),effs,t)
      ensures IsSafe(r,s,BinaryApp(op,e1,e2),t)
      ensures getEffects(BinaryApp(op,e1,e2),effs) == Effects.empty()
    {
      var t' :| getType(BinaryApp(op,e1,e2),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferIneq(op,e1,e2,effs) == types.Ok(Type.Bool(AnyBool));
      assert Typechecker(ets,acts,reqty).ensureIntType(e1,effs).Ok?;
      assert Typesafe(e1,effs,Type.Int);
      assert Typechecker(ets,acts,reqty).ensureIntType(e2,effs).Ok?;
      assert Typesafe(e2,effs,Type.Int);
      assert IsSafe(r,s,e1,Type.Int) by { Sound(e1,Type.Int,effs); }
      assert IsSafe(r,s,e2,Type.Int) by { Sound(e2,Type.Int,effs); }
      assert IsSafe(r,s,BinaryApp(op,e1,e2),t') by { IneqSafe(r,s,op,e1,e2); }
      assert IsSafe(r,s,BinaryApp(op,e1,e2),t) by {
        SubtyCompat(t',t);
        SemSubtyTransport(r,s,BinaryApp(op,e1,e2),t',t);
      }
    }

    lemma SoundArith(op: BinaryOp, e1: Expr, e2: Expr, t: Type, effs: Effects)
      decreases BinaryApp(op,e1,e2) , 0
      requires op == Add || op == Sub
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(BinaryApp(op,e1,e2),effs,t)
      ensures IsSafe(r,s,BinaryApp(op,e1,e2),t)
      ensures getEffects(BinaryApp(op,e1,e2),effs) == Effects.empty()
    {
      var t' :| getType(BinaryApp(op,e1,e2),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferArith2(op,e1,e2,effs) == types.Ok(Type.Int);
      assert Typechecker(ets,acts,reqty).ensureIntType(e1,effs).Ok?;
      assert Typesafe(e1,effs,Type.Int);
      assert Typechecker(ets,acts,reqty).ensureIntType(e2,effs).Ok?;
      assert Typesafe(e2,effs,Type.Int);
      assert IsSafe(r,s,e1,Type.Int) by { Sound(e1,Type.Int,effs); }
      assert IsSafe(r,s,e2,Type.Int) by { Sound(e2,Type.Int,effs); }
      assert IsSafe(r,s,BinaryApp(op,e1,e2),t') by { ArithSafe(r,s,op,e1,e2); }
      assert IsSafe(r,s,BinaryApp(op,e1,e2),t) by {
        SubtyCompat(t',t);
        SemSubtyTransport(r,s,BinaryApp(op,e1,e2),t',t);
      }
    }

    lemma SoundContainsAnyAll(op: BinaryOp, e1: Expr, e2: Expr, t: Type, effs: Effects)
      decreases BinaryApp(op,e1,e2) , 0
      requires op == ContainsAny || op == ContainsAll
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(BinaryApp(op,e1,e2),effs,t)
      ensures IsSafe(r,s,BinaryApp(op,e1,e2),t)
      ensures getEffects(BinaryApp(op,e1,e2),effs) == Effects.empty()
    {
      var t' :| getType(BinaryApp(op,e1,e2),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferContainsAnyAll(op,e1,e2,effs) == types.Ok(t');
      var t1 := Typechecker(ets,acts,reqty).inferSetType(e1,effs).value;
      var t2 := Typechecker(ets,acts,reqty).inferSetType(e2,effs).value;
      assert Typesafe(e1,effs,Type.Set(t1)) by { SubtyRefl(Type.Set(t1)); }
      assert Typesafe(e2,effs,Type.Set(t2)) by { SubtyRefl(Type.Set(t2)); }
      assert IsSafe(r,s,e1,Type.Set(t1)) by { Sound(e1,Type.Set(t1),effs); }
      assert IsSafe(r,s,e2,Type.Set(t2)) by { Sound(e2,Type.Set(t2),effs); }
      assert IsSafe(r,s,BinaryApp(op,e1,e2),t') by { ContainsAnyAllSafe(r,s,op,e1,e2,t1,t2); }
      assert IsSafe(r,s,BinaryApp(op,e1,e2),t) by {
        SubtyCompat(t',t);
        SemSubtyTransport(r,s,BinaryApp(op,e1,e2),t',t);
      }
    }

    lemma SoundContains(e1: Expr, e2: Expr, t: Type, effs: Effects)
      decreases BinaryApp(Contains,e1,e2) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(BinaryApp(Contains,e1,e2),effs,t)
      ensures IsSafe(r,s,BinaryApp(Contains,e1,e2),t)
      ensures getEffects(BinaryApp(Contains,e1,e2),effs) == Effects.empty()
    {
      var t' :| getType(BinaryApp(Contains,e1,e2),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferContains(e1,e2,effs) == types.Ok(t');
      var t1 := Typechecker(ets,acts,reqty).inferSetType(e1,effs).value;
      assert Typesafe(e1,effs,Type.Set(t1)) by { SubtyRefl(Type.Set(t1)); }
      var (t2,_) := Typechecker(ets,acts,reqty).infer(e2,effs).value;
      assert Typesafe(e2,effs,t2) by { SubtyRefl(t2); }
      assert IsSafe(r,s,e1,Type.Set(t1)) by { Sound(e1,Type.Set(t1),effs); }
      assert IsSafe(r,s,e2,t2) by { Sound(e2,t2,effs); }
      assert IsSafe(r,s,BinaryApp(Contains,e1,e2),t') by { ContainsSetSafe(r,s,e1,e2,t1,t2); }
      assert IsSafe(r,s,BinaryApp(Contains,e1,e2),t) by { SemSubtyTransport(r,s,BinaryApp(Contains,e1,e2),t',t); }
    }

    lemma InferRecordLemma(e: Expr, es: seq<(Attr,Expr)>, effs: Effects)
      requires forall i | 0 <= i < |es| :: es[i] < e
      requires Typechecker(ets,acts,reqty).inferRecord(e,es,effs).Ok?
      ensures forall i | 0 <= i < |es| :: es[i].0 in Typechecker(ets,acts,reqty).inferRecord(e,es,effs).value.attrs.Keys && Typechecker(ets,acts,reqty).infer(es[i].1,effs).Ok?
      ensures forall k | k in Typechecker(ets,acts,reqty).inferRecord(e,es,effs).value.attrs.Keys :: KeyExists(k,es) && Typechecker(ets,acts,reqty).infer(LastOfKey(k,es),effs).value.0 == Typechecker(ets,acts,reqty).inferRecord(e,es,effs).value.attrs[k].ty
      ensures forall k | !(k in Typechecker(ets,acts,reqty).inferRecord(e,es,effs).value.attrs.Keys) :: !KeyExists(k,es)
    {
      reveal Typechecker(ets,acts,reqty).inferRecord();
    }

    lemma SoundRecord(es: seq<(Attr,Expr)>, t: Type, effs: Effects)
      decreases Expr.Record(es) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(Expr.Record(es),effs,t)
      ensures IsSafe(r,s,Expr.Record(es),t)
      ensures getEffects(Expr.Record(es),effs) == Effects.empty()
    {
      var t' :| getType(Expr.Record(es),effs) == t' && subty(t',t);
      var rt := Typechecker(ets,acts,reqty).inferRecord(Expr.Record(es),es,effs).value;
      InferRecordLemma(Expr.Record(es),es,effs);
      assert t' == Type.Record(rt);
      assert forall i | 0 <= i < |es| :: WellTyped(es[i].1,effs);
      assert forall k | k in rt.attrs :: KeyExists(k,es) && getType(LastOfKey(k,es),effs) == rt.attrs[k].ty by {
        assert Typechecker(ets,acts,reqty).inferRecord(Expr.Record(es),es,effs).Ok?;
      }
      forall k | k in rt.attrs
        ensures KeyExists(k,es) && IsSafe(r,s,LastOfKey(k,es),rt.attrs[k].ty)
      {
        assert getType(LastOfKey(k,es),effs) == rt.attrs[k].ty;
        assert Typesafe(LastOfKey(k,es),effs,rt.attrs[k].ty) by { SubtyRefl(rt.attrs[k].ty); }
        assert IsSafe(r,s,LastOfKey(k,es),rt.attrs[k].ty) by { Sound(LastOfKey(k,es),rt.attrs[k].ty,effs); }
      }
      assert IsSafe(r,s,Expr.Record(es),t') by {
        assert forall ae | ae in es :: ExistsSafeType(r,s,ae.1) by {
          forall ae | ae in es
            ensures ExistsSafeType(r,s,ae.1)
          {
            assert WellTyped(ae.1,effs);
            var t_ae := getType(ae.1,effs);
            assert Typesafe(ae.1,effs,t_ae) by { SubtyRefl(t_ae); }
            assert IsSafe(r,s,ae.1,t_ae) by { Sound(ae.1,t_ae,effs); }
          }
        }
        RecordSafe(r,s,es,rt);
      }
      assert IsSafe(r,s,Expr.Record(es),t) by {
        SubtyCompat(t',t);
        SemSubtyTransport(r,s,Expr.Record(es),t',t);
      }
    }

    lemma InferSetLemma(e: Expr, es: seq<Expr>, effs: Effects)
      requires forall i | 0 <= i < |es| :: es[i] < e
      requires Typechecker(ets,acts,reqty).inferSet(e,es,effs).Ok?
      ensures forall i | 0 <= i < |es| :: Typechecker(ets,acts,reqty).infer(es[i],effs).Ok? && subty(Typechecker(ets,acts,reqty).infer(es[i],effs).value.0,Typechecker(ets,acts,reqty).inferSet(e,es,effs).value)
    {
      if es == [] {
      } else {
        var (t,_) := Typechecker(ets,acts,reqty).infer(es[0],effs).value;
        var t1 := Typechecker(ets,acts,reqty).inferSet(e,es[1..],effs).value;
        var t2 := lubOpt(t,t1).value;
        assert forall i | 0 <= i < |es| :: Typechecker(ets,acts,reqty).infer(es[i],effs).Ok? && subty(Typechecker(ets,acts,reqty).infer(es[i],effs).value.0,t2) by {
          forall i | 0 <= i < |es|
            ensures Typechecker(ets,acts,reqty).infer(es[i],effs).Ok? && subty(Typechecker(ets,acts,reqty).infer(es[i],effs).value.0,t2)
          {
            if i == 0 {
              assert subty(t,t2) by { LubIsUB(t,t1,t2); }
            } else {
              assert Typechecker(ets,acts,reqty).infer(es[i],effs).Ok?;
              assert subty(Typechecker(ets,acts,reqty).infer(es[i],effs).value.0,t2) by {
                LubIsUB(t,t1,t2);
                SubtyTrans(Typechecker(ets,acts,reqty).infer(es[i],effs).value.0,t1,t2);
              }
            }
          }
        }
      }
    }

    lemma SoundSet(es: seq<Expr>, t: Type, effs: Effects)
      decreases Expr.Set(es) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires Typesafe(Expr.Set(es),effs,t)
      requires EffectsInvariant(effs)
      ensures IsSafe(r,s,Expr.Set(es),t)
      ensures getEffects(Expr.Set(es),effs) == Effects.empty()
    {
      var t' :| getType(Expr.Set(es),effs) == t' && subty(t',t);
      var st := Typechecker(ets,acts,reqty).inferSet(Expr.Set(es),es,effs).value;
      InferSetLemma(Expr.Set(es),es,effs);
      assert t' == Type.Set(st);
      forall i | 0 <= i < |es|
        ensures IsSafe(r,s,es[i],st)
      {
        InterpretSetLemma(es,r,s);
        assert Typesafe(es[i],effs,st);
        Sound(es[i],st,effs);
      }
      assert IsSafe(r,s,Expr.Set(es),t') by {
        SetConstrSafe(r,s,es,st);
      }
      assert IsSafe(r,s,Expr.Set(es),t) by {
        SubtyCompat(t',t);
        SemSubtyTransport(r,s,Expr.Set(es),t',t);
      }
    }

    lemma SoundGetAttr(e: Expr, k: Attr, t: Type, effs: Effects)
      decreases GetAttr(e,k) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(GetAttr(e,k),effs,t)
      ensures IsSafe(r,s,GetAttr(e,k),t)
      ensures getEffects(GetAttr(e,k),effs) == Effects.empty()
    {
      var t' :| getType(GetAttr(e,k),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferGetAttr(e,k,effs).Ok?;
      var ret := Typechecker(ets,acts,reqty).inferRecordEntityType(e,effs).value;
      match ret {
        case Record(rt) => {
          assert t' == rt.attrs[k].ty;
          assert Typesafe(e,effs,Type.Record(rt)) by { SubtyRefl(Type.Record(rt)); }
          assert IsSafe(r,s,e,Type.Record(rt)) by { Sound(e,Type.Record(rt),effs); }
          assert IsSafe(r,s,GetAttr(e,k),t') by {
            assert k in rt.attrs;
            assert rt.attrs[k].isRequired || effs.contains(e,k);
            if rt.attrs[k].isRequired {
              ObjectProjSafeRequired(r,s,e,Type.Record(rt),k,rt.attrs[k]);
            } else {
              reveal EffectsInvariant();
              assert GetAttrSafe(r,s,e,k);
              ObjectProjSafeGetAttrSafe(r,s,e,Type.Record(rt),k,rt.attrs[k]);
            }
          }
          assert IsSafe(r,s,GetAttr(e,k),t) by {
            SubtyCompat(t',t);
            SemSubtyTransport(r,s,GetAttr(e,k),t',t);
          }
        }
        case Entity(lub) => {
          var rt := ets.getLubRecordType(lub).value;
          assert t' == rt.attrs[k].ty;
          assert IsSafe(r,s,e,Type.Entity(lub)) by { Sound(e,Type.Entity(lub),effs); }
          assert IsSafe(r,s,GetAttr(e,k),t') by {
            assert k in rt.attrs;
            assert rt.attrs[k].isRequired || effs.contains(e,k);
            if !rt.attrs[k].isRequired {
              reveal EffectsInvariant();
              assert GetAttrSafe(r,s,e,k);
            }
            forall euid: EntityUID | InstanceOfType(Primitive(Primitive.EntityUID(euid)),Type.Entity(lub)) && euid in s.entities
              ensures rt.attrs[k].isRequired ==> k in s.entities[euid].attrs
              ensures k in s.entities[euid].attrs ==> InstanceOfType(s.entities[euid].attrs[k],t')
            {
              GetLubRecordTypeSubty(lub, euid.ty);
              SubtyCompat(ets.types[euid.ty].attrs[k].ty, t');
            }
            EntityProjSafe(r,s,e,k,lub,t',rt.attrs[k].isRequired);
          }
          assert IsSafe(r,s,GetAttr(e,k),t) by {
            SubtyCompat(t',t);
            SemSubtyTransport(r,s,GetAttr(e,k),t',t);
          }
        }
      }
    }

    lemma LubRecordTypeSubty(rt1: RecordType, rt2: RecordType)
      ensures subtyRecordType(rt1, lubRecordType(rt1, rt2).value)
      ensures subtyRecordType(rt2, lubRecordType(rt1, rt2).value)
    {
      var rtl := lubRecordType(rt1, rt2).value;

      assert rt1.isOpen() ==> rtl.isOpen();
      assert rt2.isOpen() ==> rtl.isOpen();
      assert !rtl.isOpen() ==> rt1.attrs.Keys == rt2.attrs.Keys;

      forall k | k in rtl.attrs.Keys
        ensures subtyAttrType(rt1.attrs[k], rtl.attrs[k]) && subtyAttrType(rt2.attrs[k], rtl.attrs[k]) {
        var al := rtl.attrs[k];
        var a1 := rt1.attrs[k];
        var a2 := rt2.attrs[k];

        var al' := lubOpt(a1.ty,a2.ty);
        assert al'.Ok?;
        assert al'.value == al.ty;

        LubIsUB(a1.ty, a2.ty, al.ty);
      }
    }

    lemma LubRecordTypeSeqSubty(rts: seq<RecordType>, i: nat)
      requires lubRecordTypeSeq(rts).Ok?
      requires 0 <= i < |rts|
      ensures subtyRecordType(rts[i], lubRecordTypeSeq(rts).value)
    {
      var res := lubRecordTypeSeq(rts).value;
      if |rts| == 1 {
        SubtyRecordTypeRefl(rts[0]);
      } else {
        var tailRes := lubRecordTypeSeq(rts[1..]).value;
        LubRecordTypeSubty(rts[0], tailRes);
        if i > 0 {
          LubRecordTypeSeqSubty(rts[1..], i - 1);
          SubtyRecordTypeTrans(rts[i], tailRes, res);
        }
      }
    }

    lemma GetLubRecordTypeSubty(lub: EntityLUB, ety: EntityType)
      requires lub.EntityLUB?
      requires ety in lub.tys
      requires ets.getLubRecordType(lub).Ok?
      requires ety in ets.types
      ensures subtyRecordType(ets.types[ety], ets.getLubRecordType(lub).value)
    {
      var lub_ty := ets.getLubRecordType(lub) ;
      if lub_ty != Ok(RecordType(map[], OpenAttributes)) {
        def.util.EntityTypeLeqIsTotalOrder();
        var lubSeq := def.util.SetToSortedSeq(lub.tys,def.util.EntityTypeLeq);
        var etyI :| 0 <= etyI < |lubSeq| && lubSeq[etyI] == ety;
        var RecordTypeSeq := seq (|lubSeq|, i requires 0 <= i < |lubSeq| => ets.types[lubSeq[i]]);
        LubRecordTypeSeqSubty(RecordTypeSeq, etyI);
      }
    }

    lemma SoundHasAttr(e: Expr, k: Attr, t: Type, effs: Effects)
      decreases HasAttr(e,k) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(HasAttr(e,k),effs,t)
      ensures IsSafe(r,s,HasAttr(e,k),t)
      ensures GuardedEffectsInvariant(HasAttr(e,k),getEffects(HasAttr(e,k),effs))
    {
      var t' :| getType(HasAttr(e,k),effs) == t' && subty(t',t);
      assert Typechecker(ets,acts,reqty).inferHasAttr(e,k,effs).Ok?;
      var ret := Typechecker(ets,acts,reqty).inferRecordEntityType(e,effs).value;
      assert GuardedEffectsInvariant(HasAttr(e,k),Effects.empty()) by {
        EmptyEffectsInvariant();
      }
      match ret {
        case Record(rt) => {
          assert Typesafe(e,effs,Type.Record(rt)) by { SubtyRefl(Type.Record(rt)); }
          assert IsSafe(r,s,e,Type.Record(rt)) by { Sound(e,Type.Record(rt),effs); }
          if k in rt.attrs {
            if rt.attrs[k].isRequired {
              assert IsSafe(r,s,e,Type.Record(RecordType(map[k := rt.attrs[k]], OpenAttributes))) by {
                SubtyRefl(rt.attrs[k].ty);
                assert subtyRecordType(rt,RecordType(map[k := rt.attrs[k]], OpenAttributes));
                assert subty(Type.Record(rt),Type.Record(RecordType(map[k := rt.attrs[k]], OpenAttributes)));
                SubtyCompat(Type.Record(rt),Type.Record(RecordType(map[k := rt.attrs[k]], OpenAttributes)));
                SemSubtyTransport(r,s,e,Type.Record(rt),Type.Record(RecordType(map[k := rt.attrs[k]], OpenAttributes)));
              }
              assert IsSafe(r,s,HasAttr(e,k),t') by { RecordHasRequiredTrueSafe(r,s,e,k,rt.attrs[k]); }
            } else if effs.contains(e,k) {
              assert IsSafe(r,s,HasAttr(e,k),t') by {
                reveal EffectsInvariant();
              }
            } else {
              assert IsSafe(r,s,e,Type.Record(RecordType(map[], OpenAttributes))) by {
                assert subty(Type.Record(rt),Type.Record(RecordType(map[], OpenAttributes)));
                SubtyCompat(Type.Record(rt),Type.Record(RecordType(map[], OpenAttributes)));
                SemSubtyTransport(r,s,e,Type.Record(rt),Type.Record(RecordType(map[], OpenAttributes)));
              }
              assert IsSafe(r,s,HasAttr(e,k),t') by { RecordHasOpenRecSafe(r,s,e,k); }
              assert GuardedEffectsInvariant(HasAttr(e,k),Effects.singleton(e,k)) by {
                if IsTrueStrong(r,s,HasAttr(e,k)) {
                  IsTrueStrongImpliesIsTrue(r,s,HasAttr(e,k));
                  reveal EffectsInvariant();
                }
              }
            }
          } else if rt.isOpen() {
            assert IsSafe(r,s,e,Type.Record(RecordType(map[], OpenAttributes))) by {
              assert subty(Type.Record(rt),Type.Record(RecordType(map[], OpenAttributes)));
              SubtyCompat(Type.Record(rt),Type.Record(RecordType(map[], OpenAttributes)));
              SemSubtyTransport(r,s,e,Type.Record(rt),Type.Record(RecordType(map[], OpenAttributes)));
            }
            assert IsSafe(r,s,HasAttr(e,k),t') by { RecordHasOpenRecSafe(r,s,e,k); }
          } else {
            assert IsSafe(r,s,HasAttr(e,k),t') by { RecordHasClosedRecFalseSafe(r,s,e,k, rt); }
          }
        }
        case Entity(et) => {
          assert Typesafe(e,effs,Type.Entity(et)) by { SubtyRefl(Type.Entity(et)); }
          assert IsSafe(r,s,e,Type.Entity(et)) by { Sound(e,Type.Entity(et),effs); }
          if !ets.isAttrPossible(et,k) {
            EntityHasImpossibleFalseSafe(r,s,e,k,et);
          } else {
            var m := ets.getLubRecordType(et).value;
            if k in m.attrs {
              if effs.contains(e,k) {
                assert IsSafe(r,s,HasAttr(e,k),t') by {
                  reveal EffectsInvariant();
                }
              } else {
                assert IsSafe(r,s,e,Type.Entity(AnyEntity)) by {
                  SubtyCompat(Type.Entity(et),Type.Entity(AnyEntity));
                  SemSubtyTransport(r,s,e,Type.Entity(et),Type.Entity(AnyEntity));
                }
                assert IsSafe(r,s,HasAttr(e,k),t') by { EntityHasOpenSafe(r,s,e,k); }
                assert GuardedEffectsInvariant(HasAttr(e,k),Effects.singleton(e,k)) by {
                  if IsTrueStrong(r,s,HasAttr(e,k)) {
                    IsTrueStrongImpliesIsTrue(r,s,HasAttr(e,k));
                    reveal EffectsInvariant();
                  }
                }
              }
            } else {
              PossibleAttrNotInLubAttrImpliesOpen(et, k, m);
              assert IsSafe(r,s,e,Type.Entity(AnyEntity)) by {
                SubtyCompat(Type.Entity(et),Type.Entity(AnyEntity));
                SemSubtyTransport(r,s,e,Type.Entity(et),Type.Entity(AnyEntity));
              }
              assert IsSafe(r,s,HasAttr(e,k),t') by { EntityHasOpenSafe(r,s,e,k); }
            }
          }
        }
      }
      assert IsSafe(r,s,HasAttr(e,k),t) by {
        SubtyCompat(t',t);
        SemSubtyTransport(r,s,HasAttr(e,k),t',t);
      }
    }

    lemma PossibleAttrNotInLubAttrImpliesOpen(lub: EntityLUB, k: Attr, lubR: RecordType)
      requires ets.getLubRecordType(lub) == Ok(lubR)
      requires ets.isAttrPossible(lub, k)
      requires k !in lubR.attrs.Keys
      ensures lubR.isOpen()
    {
      if lub.AnyEntity? || exists et <- lub.tys :: isAction(et) {
        assert ets.getLubRecordType(AnyEntity) == Ok(RecordType(map[], OpenAttributes));
      } else {
        assert forall et <- lub.tys :: et in ets.types;
        assert exists et <- lub.tys :: et in ets.types && (ets.types[et].isOpen() || k in ets.types[et].attrs);
        var et :| et in lub.tys && et in ets.types && (ets.types[et].isOpen() || k in ets.types[et].attrs);
        GetLubRecordTypeSubty(lub, et);
        assert lubR.isOpen();
      }
    }

    lemma SoundInSetMemberFalse(e1: Expr, ei2s: seq<Expr>, i: nat, effs: Effects)
      decreases BinaryApp(BinaryOp.In,e1,Expr.Set(ei2s)) , 0 , Expr.Set(ei2s) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires WellTyped(BinaryApp(BinaryOp.In,e1,Expr.Set(ei2s)),effs)
      requires getType(BinaryApp(BinaryOp.In,e1,Expr.Set(ei2s)),effs) == Type.Bool(False)
      requires !Typechecker(ets,acts,reqty).isUnspecifiedVar(e1)
      requires 0 <= i < |ei2s|
      ensures IsFalse(r,s,BinaryApp(BinaryOp.In,e1,ei2s[i]))
    {
      // Reestablishing things we had at the call site in `SoundIn`.
      var e2 := Expr.Set(ei2s);
      var typechecker := Typechecker(ets,acts,reqty);
      assert typechecker.inferIn(BinaryApp(BinaryOp.In,e1,e2),e1,e2,effs) == types.Ok(Type.Bool(False));

      assert typechecker.ensureEntityType(e1,effs).Ok?;
      var t1 := getType(e1,effs);

      var euids2 :- assert typechecker.tryGetEUIDs(e2);
      var ets2 := set u <- euids2 :: u.ty;

      // New proof.
      var u2 :- assert typechecker.tryGetEUID(ei2s[i]);
      assert u2 in euids2;
      match e1 {
        case Var(v1) =>
          var et1 :- assert typechecker.getPrincipalOrResource(v1);
          assert t1 == Type.Entity(EntityLUB({et1}));
          assert IsSafe(r,s,Var(v1),t1) by { Sound(e1,t1,effs); }
          assert !ets.possibleDescendantOf(et1,u2.ty);
          InSingleFalseEntityTypeAndLiteral(r,s,e1,et1,u2);
        case PrimitiveLit(EntityUID(u1)) =>
          if isAction(u1.ty) {
            assert !acts.descendantOfSet(u1,euids2);
            assert !acts.descendantOf(u1,u2);
          } else {
            assert !ets.possibleDescendantOfSet(u1.ty,ets2);
            assert !ets.possibleDescendantOf(u1.ty,u2.ty);
          }
          InSingleFalseLiterals(r,s,u1,u2);
      }
    }

    lemma SoundIn(e1: Expr, e2: Expr, t: Type, effs: Effects)
      decreases BinaryApp(BinaryOp.In,e1,e2) , 0 , e2
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(BinaryApp(BinaryOp.In,e1,e2),effs,t)
      ensures IsSafe(r,s,BinaryApp(BinaryOp.In,e1,e2),t)
      ensures getEffects(BinaryApp(BinaryOp.In,e1,e2),effs) == Effects.empty()
    {
      var t' :| getType(BinaryApp(BinaryOp.In,e1,e2),effs) == t' && subty(t',t);
      var typechecker := Typechecker(ets,acts,reqty);
      assert typechecker.inferIn(BinaryApp(BinaryOp.In,e1,e2),e1,e2,effs) == types.Ok(t');

      assert typechecker.ensureEntityType(e1,effs).Ok?;
      var t1 := getType(e1,effs);
      assert t1.Entity?;
      assert subty(t1,Type.Entity(AnyEntity));
      assert IsSafe(r,s,e1,Type.Entity(AnyEntity)) by { Sound(e1,Type.Entity(AnyEntity),effs); }

      assert typechecker.ensureEntitySetType(e2,effs).Ok?;
      var t2 := getType(e2,effs);
      var e2IsSet := match t2 {
        case Entity(_) => false
        case Set(Entity(_)) => true
        case Set(Never) => true
      };
      var e2IsSpecified := match t2 {
        case Entity(lub) => lub.specified()
        case Set(Entity(lub)) => lub.specified()
        case Set(Never) => true
      };

      match t' {
        // Easy case
        case Bool(AnyBool) =>
          assert IsSafe(r,s,BinaryApp(BinaryOp.In,e1,e2),Type.Bool(AnyBool)) by {
            if e2IsSet {
              assert IsSafe(r,s,e2,Type.Set(Type.Entity(AnyEntity))) by { Sound(e2,Type.Set(Type.Entity(AnyEntity)),effs); }
              InSetSafe(r,s,e1,e2);
            } else {
              assert IsSafe(r,s,e2,Type.Entity(AnyEntity)) by { Sound(e2,Type.Entity(AnyEntity),effs); }
              InSingleSafe(r,s,e1,e2);
            }
          }
        // Harder case: we have to prove that the result is false.
        case Bool(False) =>
          if typechecker.isUnspecifiedVar(e1) && e2IsSpecified {
            UnspecifiedVarHasUnspecifiedEntityType(e1);
            assert IsSafe(r,s,e2,t2) by { Sound(e2,t2,effs); }
            if e2IsSet {
              var Set(t2e) := t2;
              InSetFalseTypes(r,s,e1,e2,unspecifiedEntityType,t2e);
            } else {
              InSingleFalseTypes(r,s,e1,e2,unspecifiedEntityType,t2);
            }
          } else {
            match e2 {
              case PrimitiveLit(EntityUID(u2)) => match e1 {
                case Var(v1) =>
                  var et1 :- assert typechecker.getPrincipalOrResource(v1);
                  assert t1 == Type.Entity(EntityLUB({et1}));
                  assert IsSafe(r,s,Var(v1),t1) by { Sound(e1,t1,effs); }
                  assert !ets.possibleDescendantOf(et1,u2.ty);
                  InSingleFalseEntityTypeAndLiteral(r,s,e1,et1,u2);
                case PrimitiveLit(EntityUID(u1)) =>
                  if isAction(u1.ty) {
                    assert !acts.descendantOf(u1,u2);
                  } else {
                    assert !ets.possibleDescendantOf(u1.ty,u2.ty);
                  }
                  InSingleFalseLiterals(r,s,u1,u2);
              }
              case Set(ei2s) =>
                var euids2 :- assert typechecker.tryGetEUIDs(e2);
                var ets2 := set u <- euids2 :: u.ty;
                // Argument that is the same any time e2 is a set.
                assert e2IsSet;
                var eltType :| t2 == Type.Set(eltType);
                InferSetLemma(e2, ei2s, effs);
                forall i | 0 <= i < |ei2s|
                  ensures IsSafe(r,s,ei2s[i],Type.Entity(AnyEntity))
                {
                  assert subty(getType(ei2s[i],effs), eltType);
                  SubtyTrans(getType(ei2s[i],effs), eltType, Type.Entity(AnyEntity));
                  assert IsSafe(r,s,ei2s[i],Type.Entity(AnyEntity)) by { Sound(ei2s[i], Type.Entity(AnyEntity), effs); }
                }
                // Argument depending on e1
                forall i | 0 <= i < |ei2s|
                  ensures IsFalse(r,s,BinaryApp(BinaryOp.In,e1,ei2s[i]))
                {
                  // Since this is the most expensive part of the proof, we move
                  // it to a separate lemma to help keep each lemma under the
                  // verification limits.
                  SoundInSetMemberFalse(e1, ei2s, i, effs);
                }
                InSetFalseIfAllFalse(r,s,e1,ei2s);
            }
          }
      }

      assert IsSafe(r,s,BinaryApp(BinaryOp.In,e1,e2),t) by {
        SubtyCompat(t',t);
        SemSubtyTransport(r,s,BinaryApp(BinaryOp.In,e1,e2),t',t);
      }
    }

    lemma InferCallArgsSound(e: Expr, name: base.Name, args: seq<Expr>, tys: seq<Type>, effs: Effects)
      requires |args| == |tys|
      requires forall i | 0 <= i < |args| :: args[i] < e
      requires Typechecker(ets,acts,reqty).inferCallArgs(e,args,tys,effs).Ok?
      ensures forall i | 0 <= i < |args| :: Typesafe(args[i],effs,tys[i])
    {}

    lemma SoundCall(name: base.Name, es: seq<Expr>, t: Type, effs: Effects)
      decreases Call(name,es) , 0
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(Call(name,es),effs,t)
      ensures IsSafe(r,s,Call(name,es),t)
      ensures getEffects(Call(name,es),effs) == Effects.empty()
    {
      assert Typechecker(ets,acts,reqty).inferCall(Call(name,es),name,es,effs).Ok?;
      var eft := extFunTypes[name];
      InferCallArgsSound(Call(name,es),name,es,eft.args,effs);
      forall i | 0 <= i < |es| ensures IsSafe(r,s,es[i],eft.args[i]) {
        Sound(es[i],eft.args[i],effs);
      }
      CallSafe(r,s,name,es);
    }

    lemma Sound(e: Expr, t: Type, effs: Effects)
      decreases e , 1
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires EffectsInvariant(effs)
      requires Typesafe(e,effs,t)
      ensures IsSafe(r,s,e,t)
      ensures GuardedEffectsInvariant(e,getEffects(e,effs))
    {
      assert GuardedEffectsInvariant(e,Effects.empty()) by {
        EmptyEffectsInvariant();
      }
      match e {
        case PrimitiveLit(p) => SoundLit(p,t,effs);
        case Var(x) => SoundVar(x,t,effs);
        case If(e',e1,e2) => SoundIf(e',e1,e2,t,effs);
        case And(e1,e2) => SoundAnd(e1,e2,t,effs);
        case Or(e1,e2) => SoundOr(e1,e2,t,effs);
        case UnaryApp(Not,e') => SoundNot(e',t,effs);
        case UnaryApp(Neg,e') => SoundNeg(e',t,effs);
        case UnaryApp(MulBy(i),e') => SoundMulBy(i,e',t,effs);
        case UnaryApp(Like(p),e') => SoundLike(e',p,t,effs);
        case BinaryApp(Eq,e1,e2) => SoundEq(e1,e2,t,effs);
        case BinaryApp(Less,e1,e2) => SoundIneq(Less,e1,e2,t,effs);
        case BinaryApp(LessEq,e1,e2) => SoundIneq(BinaryOp.LessEq,e1,e2,t,effs);
        case BinaryApp(Add,e1,e2) => SoundArith(Add,e1,e2,t,effs);
        case BinaryApp(Sub,e1,e2) => SoundArith(Sub,e1,e2,t,effs);
        case BinaryApp(In,e1,e2) => SoundIn(e1,e2,t,effs);
        case BinaryApp(ContainsAny,e1,e2) => SoundContainsAnyAll(ContainsAny,e1,e2,t,effs);
        case BinaryApp(ContainsAll,e1,e2) => SoundContainsAnyAll(ContainsAll,e1,e2,t,effs);
        case BinaryApp(Contains,e1,e2) => SoundContains(e1,e2,t,effs);
        case Record(es) => SoundRecord(es,t,effs);
        case Set(es) => SoundSet(es,t,effs);
        case GetAttr(e',l) => SoundGetAttr(e',l,t,effs);
        case HasAttr(e',l) => SoundHasAttr(e',l,t,effs);
        case Call(name,es) => SoundCall(name,es,t,effs);
      }
    }

    lemma SoundToplevel(e: Expr, t: Type)
      requires InstanceOfRequestType(r,reqty)
      requires InstanceOfEntityTypeStore(s,ets)
      requires InstanceOfActionStore(s,acts)
      requires Typechecker(ets,acts,reqty).typecheck(e,t).Ok?;
      ensures IsSafe(r,s,e,t)
    {
      EmptyEffectsInvariant();
      Sound(e,t,Effects.empty());
    }
  }
}
