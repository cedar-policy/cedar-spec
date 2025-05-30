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

/-!
This file defines the Result type for symbolic evaluation.
-/

namespace Cedar.SymCC

inductive Error where
  | noSuchEntityType
  | noSuchAttribute
  | typeError
  | unsupportedError

abbrev Result (α) := Except Error α

deriving instance Repr, DecidableEq, Inhabited for Error

@[simp, inline] instance coeResult : Coe α (Result α)  where
  coe a := .ok a

instance : ToString Error where
  toString e := match e with
  | .noSuchEntityType => "noSuchEntityType"
  | .noSuchAttribute => "noSuchAttribute"
  | .typeError => "typeError"
  | .unsupportedError => "unsupportedError"

end Cedar.SymCC
