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

module

public import CedarRustModel.Convert
public import Cedar.Spec.ExtFun
import all Cedar.Spec.Ext.IPAddr

/-!
Translation of the extension model's results (`src/ext.rs`) into the Lean spec;
the values themselves are translated in `CedarRustModel/Convert.lean`.
-/

namespace CedarRustModel

open Cedar.Spec Cedar.Spec.Ext
open cedar_rust_model

@[expose] public section

/-- Well-formed extension values: prefixes are at most the address width. -/
def Ext.WF : ext.Ext → Prop
  | .IPAddr (.V4 _ p) => p.val ≤ 32
  | .IPAddr (.V6 _ p) => p.val ≤ 128
  | _ => True

def ExtRes.toSpec : ext.ExtRes → Cedar.Spec.Value
  | .Bool b => .prim (.bool b)
  | .Int i => .prim (.int (Int64.ofInt i.val))
  | .Ext e => .ext (Ext.toSpec e)

end -- public section

theorem prefixOfNat_eq (w p : Nat) : prefixOfNat w p = IPAddr.IPNetPrefix.ofNat w p := rfl

end CedarRustModel
