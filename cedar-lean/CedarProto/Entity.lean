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
import Cedar

-- Message Dependencies
import CedarProto.EntityUID
import CedarProto.Value

open Proto

namespace Cedar.Spec

-- structure EntityData where
--   attrs : Map Attr Partial.Value
--   ancestors : Set EntityUID

-- NOTE: EntityData is defined in Cedar.Spec.Entities
-- however it doesn't have the uid field which is
-- needed when crafting Entities, therefore
-- we store within an intermediate representation instead

structure EntityProto where
  uid: EntityUID
  data: EntityData
deriving Inhabited

namespace EntityProto

@[inline]
def mergeUid (result: EntityProto) (x: EntityUID) : EntityProto :=
  {result with
    uid := Field.merge result.uid x
  }

@[inline]
def mergeAttrs (result: EntityProto) (x: Array (String × Value)) : EntityProto :=
  {result with
    data.attrs := Cedar.Data.Map.mk (result.data.attrs.kvs ++ x.toList)
  }

@[inline]
def mergeAncestors (result: EntityProto) (x: Array EntityUID) : EntityProto :=
  {result with
    data.ancestors := Cedar.Data.Set.mk (result.data.ancestors.elts ++ x.toList)
  }

@[inline]
def merge (x: EntityProto) (y: EntityProto) : EntityProto :=
  {x with
    uid := Field.merge x.uid y.uid
    data.attrs := Cedar.Data.Map.mk (x.data.attrs.kvs ++ y.data.attrs.kvs)
    data.ancestors := Cedar.Data.Set.mk (x.data.ancestors.elts ++ y.data.ancestors.elts)
  }

@[inline]
def parseField (t: Tag) : BParsec (MergeFn EntityProto) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType EntityUID) t.wireType
      let x: EntityUID ← Field.parse
      pure (fun s => mergeUid s x)
    | 2 =>
      (@Field.guardWireType (Proto.Map String Value)) t.wireType
      let x: Proto.Map String Value ← Field.parse
      pure (fun s => mergeAttrs s x)
    | 3 =>
      (@Field.guardWireType (Repeated EntityUID)) t.wireType
      let x: Repeated EntityUID ← Field.parse
      pure (fun s => mergeAncestors s x)
    | _ =>
      t.wireType.skip
      pure (fun s => s)

instance : Message EntityProto := {
  parseField := parseField
  merge := merge
}

end EntityProto

namespace EntityData

@[inline]
def mkWf (e: EntityData) : EntityData :=
  {e with
    attrs := Cedar.Data.Map.make e.attrs.kvs
    ancestors := Cedar.Data.Set.make e.ancestors.elts
  }


end EntityData

end Cedar.Spec
