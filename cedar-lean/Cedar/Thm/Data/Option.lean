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
# Additional Option functions and lemmas
-/

namespace Option

def mapD {α β} (f : α → β) (default : β) : Option α → β
  | .some a => f a
  | .none   => default

theorem mapD_some {α β} (f : α → β) (default : β) (a : α) :
  (Option.some a).mapD f default = f a
:= by simp only [mapD]

theorem mapD_none {α β} (f : α → β) (default : β) :
  Option.none.mapD f default = default
:= by simp only [mapD]

end Option
