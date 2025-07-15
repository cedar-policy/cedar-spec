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

import Cedar.SymCC.Factory

/-!
This file defines the ADT for representing symbolic tags.

We currently represent with two total unary functions:
* `keys : E -> Set String` maps each instance of the entity type `E` to a set of
   strings. This set represents all tags that are attached to the given instance
   of `E`.
* `vals : {"entity" : E, "tag" : String} -> T` maps pairs of E and String to a tag value
   of type `T`. This is equivalent to using a binary function of type `E -> String -> T`
   to represent tag values, but we don't need to introduce binary functions into the
   Term language.  It may be necessary to do so in the future if it turns out that
   wrapping the entity and string arguments into a value doesn't perform well enough.

With this representation, testing if an entity `e` has the tag `s` amounts to checking
if `s` is a member of `keys e`. Safely getting the value of the tag `s` for the entity
`e` amounts to returning `none` if `s` is not a member of `e`s keys set, and otherwise
returnng `vals e s`.
-/

namespace Cedar.SymCC

open Factory

structure SymTags where  -- for EntityType E:
  keys : UnaryFunction   --   keys: E -> Set String
  vals : UnaryFunction   --   vals: {"entity" : E, "tag" : String} -> T

def SymTags.hasTag (τs : SymTags) (entity tag : Term) : Term :=
  set.member tag (app τs.keys entity)

def SymTags.getTag! (τs : SymTags) (entity tag : Term) : Term := -- unchecked getTag
  app τs.vals (tagOf entity tag)

def SymTags.getTag (τs : SymTags) (entity tag : Term) : Term := -- checked getTag
  ifTrue (τs.hasTag entity tag) (τs.getTag! entity tag)

deriving instance Repr, Inhabited, DecidableEq for SymTags

end Cedar.SymCC
