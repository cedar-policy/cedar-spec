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

import Cedar.Data.SizeOf
import Cedar.Partial.Entities
import Cedar.Partial.Request
import Cedar.Partial.Value
import Cedar.Spec.Request
import Cedar.Spec.Value
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set

/-!
  The definition of `WellFormed` used by the `Partial` authorization and
  evaluation theorems
-/

namespace Cedar.Spec

open Cedar.Data

/-- All `Prim`s are structurally WellFormed. -/
def Prim.WellFormed : Spec.Prim → Prop
  | _ => true

/-- All `Ext`s are structurally WellFormed. -/
def Ext.WellFormed : Ext → Prop
  | .decimal _ => true
  | .ipaddr _  => true

def Value.WellFormed : Spec.Value → Prop
  | .prim p => p.WellFormed
  | .set s => s.WellFormed ∧ ∀ elt ∈ s, elt.WellFormed
  | .record r => r.WellFormed ∧ ∀ kv ∈ r.kvs, kv.snd.WellFormed
  | .ext x => x.WellFormed
decreasing_by
  all_goals simp_wf
  case _ h₁ => -- set
    have := Set.sizeOf_lt_of_mem h₁
    omega
  case _ h₁ => -- record
    have h₂ := Map.sizeOf_lt_of_value h₁
    apply Nat.lt_trans h₂
    have h₃ := Map.sizeOf_lt_of_kvs r
    simp [Map.kvs] at *
    omega

def Request.WellFormed : Spec.Request → Prop
  | { context, .. } => context.WellFormed ∧ ∀ val ∈ context.values, val.WellFormed

end Cedar.Spec

namespace Cedar.Partial

open Cedar.Data

mutual

def ResidualExpr.WellFormed : Partial.ResidualExpr → Prop
  | .and pv₁ pv₂
  | .or pv₁ pv₂
  | .binaryApp _ pv₁ pv₂ =>
      pv₁.WellFormed ∧ pv₂.WellFormed
  | .ite pv₁ pv₂ pv₃ =>
      pv₁.WellFormed ∧ pv₂.WellFormed ∧ pv₃.WellFormed
  | .unaryApp _ pv₁
  | .getAttr pv₁ _
  | .hasAttr pv₁ _ =>
      pv₁.WellFormed
  | .set pvs
  | .call _ pvs =>
      ∀ pv ∈ pvs, pv.WellFormed
  | .record apvs =>
      ∀ kv ∈ apvs, kv.snd.WellFormed
  | .unknown _ =>
      true
termination_by x => sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals try omega
  case _ | _ => -- set | call
    rename_i h
    have := List.sizeOf_lt_of_mem h
    omega
  case _ => -- record
    rename_i h
    exact List.sizeOf_snd_lt_sizeOf_list h

def Value.WellFormed : Partial.Value → Prop
  | .value v => v.WellFormed
  | .residual r => r.WellFormed
termination_by pv => sizeOf pv

end

def Request.WellFormed : Partial.Request → Prop
  | { context, .. } => context.WellFormed ∧ ∀ pval ∈ context.values, pval.WellFormed

def EntityData.WellFormed : Partial.EntityData → Prop
  | { attrs, ancestors } =>
      attrs.WellFormed ∧
      ancestors.WellFormed ∧
      ∀ pval ∈ attrs.values, pval.WellFormed

def Entities.WellFormed : Partial.Entities → Prop
  | { es } => es.WellFormed ∧ ∀ edata ∈ es.values, edata.WellFormed

def Subsmap.WellFormed : Subsmap → Prop
  | { m } => m.WellFormed ∧ ∀ v ∈ m.values, v.WellFormed

end Cedar.Partial
