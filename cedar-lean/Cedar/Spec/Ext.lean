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

import Cedar.Spec.Ext.Decimal
import Cedar.Spec.Ext.IPAddr

/-! This file defines Cedar extension values. -/

namespace Cedar.Spec

open Cedar.Spec.Ext

----- Definitions -----

abbrev IPAddr := IPAddr.IPNet

inductive Ext where
  | decimal (d : Decimal)
  | ipaddr (ip : IPAddr)

def Ext.lt : Ext → Ext → Bool
  | .decimal d₁, .decimal d₂ => d₁ < d₂
  | .ipaddr ip₁, .ipaddr ip₂ => ip₁ < ip₂
  | .decimal  _, .ipaddr _   => true
  | .ipaddr   _, .decimal _  => false

----- Derivations -----

deriving instance Repr for Ext
deriving instance DecidableEq for Ext

instance : LT Ext where
lt := fun x y => Ext.lt x y

instance Ext.decLt (x y : Ext) : Decidable (x < y) :=
if  h : Ext.lt x y then isTrue h else isFalse h

instance : Coe Decimal Ext where
  coe d := .decimal d

instance : Coe IPAddr Ext where
  coe a := .ipaddr a

end Cedar.Spec