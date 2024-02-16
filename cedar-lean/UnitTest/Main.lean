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

import UnitTest.Decimal
import UnitTest.IPAddr
import UnitTest.Wildcard

open UnitTest

def tests :=
  Decimal.tests ++
  IPAddr.tests ++
  Wildcard.tests

def main : IO UInt32 := do
  TestSuite.runAll tests
