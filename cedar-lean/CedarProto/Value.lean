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
import Protobuf.BParsec
import Protobuf.Message
import Protobuf.String
import Protobuf.Enum
import Protobuf.Map

import Cedar

import CedarProto.Expr

open Cedar.Spec
open Proto

namespace Cedar.Spec.Value
@[inline]
def merge (v1: Value) (v2: Value) : Value :=
  match v2 with
    | .prim _ => v2
    | .set s2 => match v1 with
      | .set s1 => Cedar.Data.Set.make (s1.elts ++ s2.elts)
      | _ => v2
    | .record m2 => match v1 with
      | .record m1 => Cedar.Data.Map.make (m1.kvs ++ m2.kvs)
      | _ => v2
    | .ext _ => v2


private partial def exprToValue : Expr → Value
  | .lit p => .prim p
  | Expr.record r => .record (Cedar.Data.Map.make (r.map (fun ⟨attr, e⟩ => ⟨attr, exprToValue e⟩)))
  | Expr.set s => .set (Cedar.Data.Set.make (s.map exprToValue))
  -- TODO: ExtFun
  | _ => panic!("exprToValue: invalid input expression")


instance : Field Value := Field.fromIntField exprToValue merge
end Cedar.Spec.Value
