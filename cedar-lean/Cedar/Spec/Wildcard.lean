/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

namespace Cedar.Spec

inductive PatElem where
  | star
  | justChar (c : Char)
deriving Repr
deriving instance DecidableEq for PatElem
deriving instance Inhabited for PatElem

abbrev Pattern := List PatElem

def charMatch (textChar : Char) (patternChar : PatElem) : Bool :=
  match patternChar with
  | .justChar c => textChar == c
  | _ => false

def wildcard (patternChar : PatElem) : Bool :=
  match patternChar with
  | .star => true
  | _ => false

def wildcardMatch (text : String) (pattern : Pattern) : Bool :=
  match pattern with
  | [] => match text with
    | .mk [] => true
    | _ => false
  | p::ps => match text with
    | .mk [] => wildcard p && wildcardMatch (.mk []) ps
    | .mk (c::cs) => match wildcard p with
      | true => wildcardMatch (.mk (c::cs)) ps || wildcardMatch (.mk cs) (p::ps)
      | false => charMatch c p && wildcardMatch (.mk cs) ps
  termination_by
    wildcardMatch text pattern => sizeOf text + sizeOf pattern

end Cedar.Spec
