/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Cedar.Spec
import Cedar.SymCC.Env

/-!

# Interpretations

An `Interpretation` is a structure that binds term variables to literal terms
and uninterpreted functions (`UUF`) to interpreted ones (`UDF`). In practice,
Interpretations are obtained from low-level models returned by SMT solvers.

When a symbolic structure (such as a term, request, function, or entities) is
interpreted with respect to an Interpretation, the result is a literal symbolic
structure.
-/

namespace Cedar.SymCC

open Data Factory Spec

/--
An Interpretation consists of three maps:
- `vars` maps variables to literal terms of the same type;
- `funs` maps uninterpreted functions to intepreted functions; and
- `partials` maps partial application terms to literals of the right type.

A partial application term represents the application of an operator to a
correctly typed literal outside of the operator's domain---for example, the
application of `option.get` to a `.none` term. The SMTLib language treats all
such operators as total, and it picks an arbitrary value of the right type as
the result of the application.
-/
structure Interpretation where
  vars : TermVar → Term
  funs : UUF → UDF
  partials : Term → Term

def UnaryFunction.interpret (I : Interpretation) : UnaryFunction → UnaryFunction
  | .uuf f => .udf (I.funs f)
  | .udf f => .udf f

def Factory.option.get' (I : Interpretation) (t : Term) : Term :=
  if let .none ty := t
  then I.partials (.app Op.option.get [.none ty] ty)
  else (Factory.option.get t)

def Factory.ext.ipaddr.addrV4' (I : Interpretation) (t : Term) : Term :=
  if let .prim (.ext (.ipaddr (.V6 ⟨v6, p6⟩))) := t
  then I.partials (.app (.ext ExtOp.ipaddr.addrV4) [.prim (.ext (.ipaddr (.V6 ⟨v6, p6⟩)))] (.bitvec 32))
  else (Factory.ext.ipaddr.addrV4 t)

def Factory.ext.ipaddr.prefixV4' (I : Interpretation) (t : Term) : Term :=
  if let .prim (.ext (.ipaddr (.V6 ⟨v6, p6⟩))) := t
  then I.partials (.app (.ext ExtOp.ipaddr.prefixV4) [.prim (.ext (.ipaddr (.V6 ⟨v6, p6⟩)))] (.option (.bitvec 5)))
  else (Factory.ext.ipaddr.prefixV4 t)

def Factory.ext.ipaddr.addrV6' (I : Interpretation) (t : Term) : Term :=
  if let .prim (.ext (.ipaddr (.V4 ⟨v4, p4⟩))) := t
  then I.partials (.app (.ext ExtOp.ipaddr.addrV6) [.prim (.ext (.ipaddr (.V4 ⟨v4, p4⟩)))] (.bitvec 128))
  else (Factory.ext.ipaddr.addrV6 t)

def Factory.ext.ipaddr.prefixV6' (I : Interpretation) (t : Term) : Term :=
  if let .prim (.ext (.ipaddr (.V4 ⟨v4, p4⟩))) := t
  then I.partials (.app (.ext ExtOp.ipaddr.prefixV6) [.prim (.ext (.ipaddr (.V4 ⟨v4, p4⟩)))] (.option (.bitvec 7)))
  else (Factory.ext.ipaddr.prefixV6 t)

def ExtOp.interpret (I : Interpretation) (op : ExtOp) (t₁ : Term) : Term :=
  match op with
  | ExtOp.decimal.val       => Factory.ext.decimal.val t₁
  | ExtOp.ipaddr.isV4       => Factory.ext.ipaddr.isV4 t₁
  | ExtOp.ipaddr.addrV4     => Factory.ext.ipaddr.addrV4' I t₁
  | ExtOp.ipaddr.prefixV4   => Factory.ext.ipaddr.prefixV4' I t₁
  | ExtOp.ipaddr.addrV6     => Factory.ext.ipaddr.addrV6' I t₁
  | ExtOp.ipaddr.prefixV6   => Factory.ext.ipaddr.prefixV6' I t₁
  | ExtOp.datetime.val      => Factory.ext.datetime.val t₁
  | ExtOp.datetime.ofBitVec => Factory.ext.datetime.ofBitVec t₁
  | ExtOp.duration.val      => Factory.ext.duration.val t₁
  | ExtOp.duration.ofBitVec => Factory.ext.duration.ofBitVec t₁

def Op.interpret (I : Interpretation) (op : Op) (ts : List Term) (ty : TermType) : Term :=
  match op, ts with
  | .not, [t₁]            => Factory.not t₁
  | .and, [t₁, t₂]        => Factory.and t₁ t₂
  | .or,  [t₁, t₂]        => Factory.or t₁ t₂
  | .eq,  [t₁, t₂]        => Factory.eq t₁ t₂
  | .ite, [t₁, t₂, t₃]    => Factory.ite t₁ t₂ t₃
  | .uuf f, [t₁]          => Factory.app (.udf (I.funs f)) t₁
  | .bvneg, [t₁]          => Factory.bvneg t₁
  | .bvadd, [t₁, t₂]      => Factory.bvadd t₁ t₂
  | .bvsub, [t₁, t₂]      => Factory.bvsub t₁ t₂
  | .bvmul, [t₁, t₂]      => Factory.bvmul t₁ t₂
  | .bvsdiv, [t₁, t₂]     => Factory.bvsdiv t₁ t₂
  | .bvsrem, [t₁, t₂]     => Factory.bvsrem t₁ t₂
  | .bvsmod, [t₁, t₂]     => Factory.bvsmod t₁ t₂
  | .bvumod, [t₁, t₂]     => Factory.bvumod t₁ t₂
  | .bvudiv, [t₁, t₂]     => Factory.bvudiv t₁ t₂
  | .bvshl, [t₁, t₂]      => Factory.bvshl t₁ t₂
  | .bvlshr, [t₁, t₂]     => Factory.bvlshr t₁ t₂
  | .bvnego, [t₁]         => Factory.bvnego t₁
  | .bvsaddo, [t₁, t₂]    => Factory.bvsaddo t₁ t₂
  | .bvssubo, [t₁, t₂]    => Factory.bvssubo t₁ t₂
  | .bvsmulo, [t₁, t₂]    => Factory.bvsmulo t₁ t₂
  | .bvslt, [t₁, t₂]      => Factory.bvslt t₁ t₂
  | .bvsle, [t₁, t₂]      => Factory.bvsle t₁ t₂
  | .bvult, [t₁, t₂]      => Factory.bvult t₁ t₂
  | .bvule, [t₁, t₂]      => Factory.bvule t₁ t₂
  | .zero_extend n, [t₁]  => Factory.zero_extend n t₁
  | Op.set.member, [t₁, t₂] => Factory.set.member t₁ t₂
  | Op.set.subset, [t₁, t₂] => Factory.set.subset t₁ t₂
  | Op.set.inter, [t₁, t₂]  => Factory.set.inter t₁ t₂
  | Op.option.get, [t₁]     => Factory.option.get' I t₁
  | Op.record.get a, [t₁]   => Factory.record.get t₁ a
  | Op.string.like p, [t₁]  => Factory.string.like t₁ p
  | .ext xop, [t₁]        => xop.interpret I t₁
  | _, _                  => .app op ts ty

def Term.interpret (I : Interpretation) : Term → Term
  | .prim p             => .prim p
  | .var v              => I.vars v
  | .none ty            => noneOf ty
  | .some t             => someOf (t.interpret I)
  | .set (Set.mk ts) ty =>
    let ts' := ts.map₁ (λ ⟨t, _⟩ => t.interpret I)
    setOf ts' ty
  | .app op ts ty       =>
    let ts' := ts.map₁ (λ ⟨t, _⟩ => t.interpret I)
    op.interpret I ts' ty
  | .record (.mk ats)   =>
    let ats' := ats.map₃ (λ ⟨(aᵢ, tᵢ), _⟩ => (aᵢ, tᵢ.interpret I))
    recordOf ats'

def SymRequest.interpret (I : Interpretation) (req : SymRequest)  : SymRequest :=
  {
    principal := req.principal.interpret I,
    action    := req.action.interpret I,
    resource  := req.resource.interpret I,
    context   := req.context.interpret I
  }

def SymTags.interpret (I : Interpretation) (τags : SymTags) : SymTags :=
  {
    keys := τags.keys.interpret I,
    vals := τags.vals.interpret I
  }

def SymEntityData.interpret (I : Interpretation) (d : SymEntityData) : SymEntityData :=
  {
    attrs     := d.attrs.interpret I,
    ancestors := d.ancestors.mapOnValues (UnaryFunction.interpret I)
    members   := d.members,
    tags      := d.tags.map (SymTags.interpret I)
  }

def SymEntities.interpret (I : Interpretation) (es : SymEntities)  : SymEntities :=
  es.mapOnValues (SymEntityData.interpret I)

def SymEnv.interpret (I : Interpretation) (env : SymEnv) : SymEnv :=
  ⟨env.request.interpret I, env.entities.interpret I⟩


end Cedar.SymCC
