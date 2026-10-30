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

public import Cedar.Spec.Response
public import Lean.Data.Json.FromToJson.Basic

/-!
This file derives `Lean.ToJson` for the specification types that DRT and the
FFI serialize. The instances live here, rather than beside the types, so that a
program that uses `Cedar.Spec` without this module doesn't link the `Lean`
package.
-/

namespace Cedar.Data

deriving instance Lean.ToJson for Set

end Cedar.Data

namespace Cedar.Spec

deriving instance Lean.ToJson for Name
deriving instance Lean.ToJson for EntityUID
deriving instance Lean.ToJson for PolicyID
deriving instance Lean.ToJson for Decision
deriving instance Lean.ToJson for Response

end Cedar.Spec
