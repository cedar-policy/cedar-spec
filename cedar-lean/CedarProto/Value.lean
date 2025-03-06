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
import Protobuf.Message

-- Message Dependencies
import CedarProto.Expr

open Proto

namespace Cedar.Spec.Value

@[inline]
def merge (v1 : Value) (v2 : Value) : Value :=
  match v1, v2 with
  | .prim (.bool b1), .prim (.bool b2) => .prim (.bool (Field.merge b1 b2))
  | .prim (.int _), .prim (.int i2) => .prim (.int i2)
  | .prim (.string s1), .prim (.string s2) => .prim (.string (Field.merge s1 s2))
  | .prim (.entityUID _), .prim (.entityUID e2) => .prim (.entityUID e2) -- todo: is this correct
  | .set s1, .set s2 => Cedar.Data.Set.make (s1.elts ++ s2.elts)
  | .record m1, .record m2 => Cedar.Data.Map.make (m1.kvs ++ m2.kvs)
  | .ext _, .ext _ => panic!("merge for Value.ext is not yet implemented")
  | _, _ => v2

private def extExprToValue (xfn : ExtFun) (args : List Expr) : Except String Value :=
  match xfn, args with
  | .decimal, [.lit (.string s)] => match Spec.Ext.Decimal.decimal s with
    | .some v => .ok $ .ext (.decimal v)
    | .none => .error s!"exprToValue: failed to parse decimal {s}"
  | .ip, [.lit (.string s)] => match Spec.Ext.IPAddr.ip s with
    | .some v => .ok $ .ext (.ipaddr v)
    | .none => .error s!"exprToValue: failed to parse ip {s}"
  | .datetime, [.lit (.string s)] => match Spec.Ext.Datetime.parse s with
    | .some v => .ok $ .ext (.datetime v)
    | .none => .error s!"exprToValue: failed to parse datetime {s}"
  | .duration, [.lit (.string s)] => match Spec.Ext.Datetime.Duration.parse s with
    | .some v => .ok $ .ext (.duration v)
    | .none => .error s!"exprToValue: failed to parse duration {s}"
  | _, _ => .error s!"exprToValue: unexpected extension value\n{repr (Expr.call xfn args)}"

partial def exprToValue : Expr → Except String Value
  | .lit p => .ok (.prim p)
  | .record r => do
      let attrs ← r.mapM λ ⟨attr, e⟩ => do .ok ⟨attr, ← exprToValue e⟩
      .ok $ .record (Cedar.Data.Map.make attrs)
  | .set s => do
      let elts ← s.mapM exprToValue
      .ok $ .set (Cedar.Data.Set.make elts)
  | .call xfn args => extExprToValue xfn args
  | e => .error s!"exprToValue: invalid input expression {repr e}"

instance : Field Value := Field.fromInterFieldFallible exprToValue merge

end Cedar.Spec.Value
