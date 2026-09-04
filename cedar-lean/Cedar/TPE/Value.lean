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

import Cedar.Spec.Value
import Cedar.Validation.Types

/-!
This file defines partial values. These are value where the attributes of records may be only
partially known.
-/

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
Possibly-partial information about one record attribute (or entity tag).
-/
inductive AttrState where
  /-- The attribute exists and its value is fully known -/
  | value (v : Value)
  /-- The attribute exists and is a record, of which only part is known -/
  | partialRecord (r : Map Attr AttrState)
  /-- The attribute exists but its value is unknown -/
  | present
  /-- The attribute is known not to exist -/
  | absent
  /-- Whether the attribute exists at all is unknown -/
  | unknown

deriving instance Repr, Inhabited for AttrState

abbrev PartialRecord := Map Attr AttrState

deriving instance Inhabited for PartialRecord

/--
The state of an attribute in a partial record.

Any attribute `r` does not list is `unknown`.
-/
def PartialRecord.attr (r : PartialRecord) (a : Attr) : AttrState :=
  (r.find? a).getD .unknown

def AttrState.exists? : AttrState → Bool
  | .value _
  | .partialRecord _
  | .present => true
  | .absent
  | .unknown => false

/--
The partial information about an attribute implied by its type.
-/
def AttrState.ofDeclared : Option QualifiedType → AttrState
  | .some (.required _) => .present
  | .some (.optional _) => .unknown
  | .none               => .absent

/--
The state an attribute in a partial record, informed by the record's declared attribute types.
-/
def PartialRecord.resolveAttr (r : PartialRecord) (a : Attr) (rty : RecordType) : AttrState :=
  match r.attr a with
  | .unknown => AttrState.ofDeclared (rty.find? a)
  | s        => s

/--
Is `r` fully concrete at the record type `rty`.

The record type tells up what attributes must be explicitly defined. All declared attribute must be
present. Optional attributes cannot be omitted, though they may be explicitly absent.
-/
def PartialRecord.isConcreteAt (r : PartialRecord) (rty : RecordType) : Bool :=
  (rty.toList.all λ (k, _) => (r.find? k).isSome) &&
  (r.toList.attach₂.all λ x =>
    match hx : x.val.snd with
    | .value _ => (rty.find? x.val.fst).isSome
    | .absent  => true
    | .partialRecord r' =>
      match (rty.find? x.val.fst).map Qualified.getType with
      | .some (.record rty') =>
        have : sizeOf r' < sizeOf r := by
          have h := x.property
          rw [hx] at h
          cases r
          simp only [Map.toList_mk_id, Map.mk.sizeOf_spec,
            AttrState.partialRecord.sizeOf_spec] at *
          omega
        PartialRecord.isConcreteAt r' rty'
      | _ => false
    | .present
    | .unknown => false)
termination_by sizeOf r

mutual

/--
The attribute as a concrete value, if it is fully known.
-/
def AttrState.asValueAt? (s : AttrState) (qty? : Option QualifiedType) : Option Value :=
  match s, qty? with
  | .value v, _ => .some v
  | .partialRecord r, .some (.required (.record rty))
  | .partialRecord r, .some (.optional (.record rty)) =>
    (PartialRecord.asValues? r rty).map Value.record
  | _, _ => .none
termination_by sizeOf s

/--
Convert to a concrete record, if it is fully known given its type.
-/
def PartialRecord.asValues? (r : PartialRecord) (rty : RecordType) : Option (Map Attr Value) :=
  if r.isConcreteAt rty
  then .some (Map.make (r.toList.attach₂.filterMap
    (λ (x : { x : Attr × AttrState // sizeOf x.snd < 1 + sizeOf r.toList }) =>
      have : sizeOf x.val.snd < sizeOf r := by
        have h := x.property
        cases r
        simp only [Map.toList_mk_id, Map.mk.sizeOf_spec] at *
        omega
      ((AttrState.asValueAt? x.val.snd (rty.find? x.val.fst)).map (Prod.mk x.val.fst)))))
  else .none
termination_by sizeOf r

end

/--
Build a partial record from a fully concrete record given its type.

Concrete records are closed, so an declared attribute not in the concrete record is known to be absent.
-/
def PartialRecord.ofConcrete (m : Map Attr Value) (rty : RecordType) : PartialRecord :=
  Map.make (
    (m.toList.map λ (k, v) => (k, AttrState.value v)) ++
    (rty.toList.filterMap λ (k, _) => if (m.find? k).isSome then none else some (k, AttrState.absent)))

/--
Build a partial record from a fully concrete set of entity tags.

Unlike attributes, tags share a single declared type and have no declared key
set, so there is nothing that lets us conclude a tag is absent.
-/
def PartialRecord.ofConcreteTags (m : Map Tag Value) : PartialRecord :=
  m.mapOnValues AttrState.value

mutual

/--
Is `s` consistent with the concrete (possibly absent) attribute value `o`?
-/
def AttrState.consistentWith (s : AttrState) (o : Option Value) : Bool :=
  match s, o with
  | .value v, .some v'                  => v == v'
  | .partialRecord r, .some (.record m) =>
    r.wellFormed && m.wellFormed && PartialRecord.consistentWith r m
  | .present, .some _                   => true
  | .absent,  .none                     => true
  | .unknown, _                         => true
  | _, _                                => false
termination_by sizeOf s

/--
Is `r` consistent with the concrete record `m`?
-/
def PartialRecord.consistentWith (r : PartialRecord) (m : Map Attr Value) : Bool :=
  r.toList.attach₂.all λ x => AttrState.consistentWith x.val.snd (m.find? x.val.fst)
termination_by sizeOf r
decreasing_by
  have h := x.property
  cases r
  simp only [Map.toList_mk_id, Map.mk.sizeOf_spec] at *
  omega

end

end Cedar.TPE
