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

import Lake
open Lake DSL

--require std from git
--  "https://github.com/leanprover/std4"@"main"

require wfinduct from git
  "https://github.com/nomeata/lean-wf-induct"

package Cedar

lean_lib Cedar where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib DiffTest where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib UnitTest where
  defaultFacets := #[LeanLib.staticFacet]

lean_exe CedarUnitTests where
  root := `UnitTest.Main

lean_exe Cli where
  root := `Cli.Main
