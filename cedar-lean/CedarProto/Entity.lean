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

import CedarProto.EntityUID
import CedarProto.Value

import Cedar
open Cedar.Spec
open Proto


-- EntityData is defined in Cedar.Spec.Entities
-- however it doesn't have the "" field which is
-- needed when crafting Entities

structure EntityProto where
  uid: EntityUID
  attrs : Cedar.Data.Map Attr Value
  ancestors : Cedar.Data.Set EntityUID
deriving Inhabited

namespace Cedar.Spec.EntityData
partial def makeWf (e: EntityData) : EntityData :=
  let newAttrs := Cedar.Data.Map.make (e.attrs.kvs.map (fun ⟨attr, v⟩ => ⟨attr, Value.makeWf v⟩))
  let newAncestors := Cedar.Data.Set.make (e.ancestors.elts)
  EntityData.mk newAttrs newAncestors
end Cedar.Spec.EntityData

namespace Cedar.Spec.EntityProto

@[inline]
def mergeUid (result: EntityProto) (x: EntityUID) : EntityProto :=
  {result with
    uid := Field.merge result.uid x
  }

@[inline]
def mergeAttrs (result: EntityProto) (x: Array (String × Value)) : EntityProto :=
  {result with
    attrs := Cedar.Data.Map.mk (result.attrs.kvs ++ x.toList)
  }

@[inline]
def mergeAncestors (result: EntityProto) (x: Array EntityUID) : EntityProto :=
  {result with
    ancestors := Cedar.Data.Set.mk (result.ancestors.elts ++ x.toList)
  }

@[inline]
def merge (x: EntityProto) (y: EntityProto) : EntityProto :=
  {x with
    uid := Field.merge x.uid y.uid
    attrs := Cedar.Data.Map.mk (x.attrs.kvs ++ y.attrs.kvs)
    ancestors := Cedar.Data.Set.mk (x.ancestors.elts ++ y.ancestors.elts)
  }


def parseField (t: Tag) : BParsec (StateM EntityProto Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType EntityUID) t.wireType
      let x: EntityUID ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeUid s x))
    | 2 =>
      (@Field.guardWireType (Array (String × Value))) t.wireType
      let x: (Array (String × Value)) ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeAttrs s x))
    | 3 =>
      (@Field.guardWireType (Repeated EntityUID)) t.wireType
      let x: Repeated EntityUID ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeAncestors s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message EntityProto := {
  parseField := parseField
  merge := merge
}

end Cedar.Spec.EntityProto
