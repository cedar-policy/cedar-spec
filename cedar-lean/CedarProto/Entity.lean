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
  attrs : Array (Attr × Value)
  ancestors : Repeated EntityUID
deriving Inhabited

namespace EntityProto

@[inline]
def toEntityData (e: EntityProto) : EntityData :=
  let newAttrs := Cedar.Data.Map.mk e.attrs.toList
  let newAncestors := Cedar.Data.Set.mk e.ancestors.toList
  EntityData.mk newAttrs newAncestors

@[inline]
def mergeUid (result: EntityProto) (x: EntityUID) : EntityProto :=
  {result with
    uid := Field.merge result.uid x
  }

@[inline]
def mergeAttrs (result: EntityProto) (x: Array (String × Value)) : EntityProto :=
  {result with
    attrs := Field.merge x result.attrs
  }

@[inline]
def mergeAncestors (result: EntityProto) (x: Array EntityUID) : EntityProto :=
  {result with
    ancestors := Field.merge x result.ancestors
  }

@[inline]
def merge (x: EntityProto) (y: EntityProto) : EntityProto :=
  {x with
    uid := Field.merge x.uid y.uid
    attrs := Field.merge y.attrs x.attrs
    ancestors := Field.merge y.ancestors x.ancestors
  }

@[inline]
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

end EntityProto

namespace EntityData

def mkWf (e: EntityData) : EntityData :=
  {e with
    attrs := Cedar.Data.Map.make (e.attrs.kvs.map (fun (ki, vi) => (ki, vi.mkWf)))
    ancestors := Cedar.Data.Set.make (e.ancestors.elts)
  }


end EntityData

end Cedar.Spec
