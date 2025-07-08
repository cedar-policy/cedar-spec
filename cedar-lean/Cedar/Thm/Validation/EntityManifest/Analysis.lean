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

import Cedar.Spec.Expr
import Cedar.Validation.Types

namespace Cedar.Thm.Validation.EntityManifest

open Cedar.Spec
open Cedar.Validation
open Cedar.Data

/--
Stores the access term's constructor and children.

Includes leaf nodes (literals, variables, and strings)
as well as attribute accesses, tag accesses, and ancestor accesses.
-/
inductive AccessTerm : Type where
  -- Literal entity ids
  | literal (euid : EntityUID)
  -- A Cedar variable
  | var (v : Var)
  -- A literal Cedar string
  | string (s : String)
  -- A record or entity attribute
  | attribute (of : AccessTerm) (attr : Attr)
  -- An entity tag access
  | tag (of : AccessTerm) (tag : AccessTerm)
  -- Whether this entity has a particular ancestor is requested
  | ancestor (of : AccessTerm) (ancestor : AccessTerm)
deriving Inhabited, Repr, DecidableEq

/--
A collection of access terms.
-/
structure AccessTerms where
  terms : Set AccessTerm := {}
deriving Inhabited, Repr

/--
Represents `AccessTerm`s possibly wrapped in record or set literals.

This allows the Entity Manifest to soundly handle
data that is wrapped in record or set literals, then used in equality
operators or dereferenced.
-/
inductive WrappedAccessTerms : Type where
  -- No access terms are needed.
  | empty
  -- A single access term, starting with a cedar variable.
  | accessTerm (term : AccessTerm)
  -- The union of two `WrappedAccessTerms`, denoting that
  -- all access terms from both are required.
  -- This is useful for join points in the analysis (`if`, set literals, etc.)
  | union (left right : WrappedAccessTerms)
  -- A record literal, each field having access terms.
  | recordLiteral (fields : Map Attr WrappedAccessTerms)
  -- A set literal containing access terms.
  -- Used to note that this type is wrapped in a literal set.
  | setLiteral (elements : WrappedAccessTerms)
  -- Intermediate values like if conditions may not be returned,
  -- but we still need to load them into the entity store.
  | withDroppedTerms (terms dropped : WrappedAccessTerms)
deriving Inhabited, Repr

namespace WrappedAccessTerms

/-- Create a WrappedAccessTerms from a Cedar variable -/
def fromVar (v : Var) : WrappedAccessTerms :=
  WrappedAccessTerms.accessTerm (AccessTerm.var v)

/-- Create a WrappedAccessTerms from an EntityUID -/
def fromEUID (euid : EntityUID) : WrappedAccessTerms :=
  WrappedAccessTerms.accessTerm (AccessTerm.literal euid)

/-- Create a WrappedAccessTerms from a string -/
def fromString (s : String) : WrappedAccessTerms :=
  WrappedAccessTerms.accessTerm (AccessTerm.string s)




mutual
  /--
  Get all access terms from this wrapped access terms,
  including dropped terms.

  This implementation uses mutual recursion with allFieldsAccessPaths to handle
  the recordLiteral case by structural recursion on the list of key-value pairs. -/
  def allAccessPaths (self : WrappedAccessTerms) : AccessTerms :=
    match self with
    | .empty => { terms := Set.empty }
    | .accessTerm term => { terms := Set.singleton term }
    | .union left right =>
        let leftTerms := allAccessPaths left
        let rightTerms := allAccessPaths right
        { terms := Set.mk (leftTerms.terms.elts ++ rightTerms.terms.elts) }
    | .recordLiteral fields =>
        -- Use the helper function that does structural recursion on the list
        allFieldsAccessPaths fields.kvs
    | .setLiteral elements =>
        allAccessPaths elements
    | .withDroppedTerms terms dropped =>
        let droppedTerms := allAccessPaths dropped
        let mainTerms := allAccessPaths terms
        { terms := Set.mk (droppedTerms.terms.elts ++ mainTerms.terms.elts) }

  /--
  Process fields of a record literal and collect all access terms.
  This function uses structural recursion on the list of key-value pairs.
  -/
  def allFieldsAccessPaths : List (Attr × WrappedAccessTerms) → AccessTerms
    | [] => { terms := Set.empty }
    | (_, field) :: rest =>
        let fieldTerms := allAccessPaths field
        let restTerms := allFieldsAccessPaths rest
        { terms := Set.mk (fieldTerms.terms.elts ++ restTerms.terms.elts) }
end


/--
Extract the access terms from a WrappedAccessTerms.
Returns None when the wrapped access terms represent a record or set literal.
-/
def returnedAccessTerms (self : WrappedAccessTerms) : Option AccessTerms :=
  match self with
  | .empty => some { terms := Set.empty }
  | .accessTerm term => some { terms := Set.singleton term }
  | .union left right =>
      match returnedAccessTerms left, returnedAccessTerms right with
      | some leftTerms, some rightTerms =>
          some { terms := Set.mk (leftTerms.terms.elts ++ rightTerms.terms.elts) }
      | _, _ => none
  | .recordLiteral _ => none
  | .setLiteral _ => none
  | .withDroppedTerms terms _ =>
      returnedAccessTerms terms

/--
Compute the cross product of two sets of access terms.
For each pair of terms, create a new tag access term.
-/
def crossProductTag (ofTerms tagTerms : AccessTerms) : List AccessTerm :=
  ofTerms.terms.elts.foldl (fun acc ofTerm =>
    acc ++ tagTerms.terms.elts.map (fun tagTerm =>
      AccessTerm.tag ofTerm tagTerm)
  ) []

/--
Get or has tag access terms.
We can safely assume that self is entity typed.
-/
def getOrHasTag (self tagTerms : WrappedAccessTerms) : WrappedAccessTerms :=
  -- Compute cross product of the access terms and the tag terms
  match returnedAccessTerms self, returnedAccessTerms tagTerms with
  | some ofAccessTerms, some tagAccessTerms =>
      -- Compute cross product of the access terms
      let tagTermsList := crossProductTag ofAccessTerms tagAccessTerms

      -- Create a union of all the new tag access terms
      let result := tagTermsList.foldl
        (fun acc term =>
          WrappedAccessTerms.union acc (WrappedAccessTerms.accessTerm term))
        WrappedAccessTerms.empty

      -- Don't forget to drop self and tag terms
      WrappedAccessTerms.withDroppedTerms
        (WrappedAccessTerms.withDroppedTerms result self)
        tagTerms
  | _, _ =>
      -- If either self or tagTerms is a record or set literal, just return empty
      -- This should never happen after typechecking
      WrappedAccessTerms.empty

/--
Access this attribute across all access terms
-/
def getOrHasAttr (self : WrappedAccessTerms) (attr : Attr) : WrappedAccessTerms :=
  match self with
  | .empty => .empty
  | .accessTerm term =>
      .accessTerm (AccessTerm.attribute term attr)
  | .recordLiteral fields =>
      match fields.find? attr with
      | some field => .withDroppedTerms field self
      | none => self
  | .setLiteral _ =>
    -- should never happen (TODO throw error?)
    self
  | .withDroppedTerms terms dropped =>
      .withDroppedTerms (terms.getOrHasAttr attr) dropped
  | .union left right =>
      .union (left.getOrHasAttr attr) (right.getOrHasAttr attr)





end WrappedAccessTerms

end Cedar.Thm.Validation.EntityManifest
