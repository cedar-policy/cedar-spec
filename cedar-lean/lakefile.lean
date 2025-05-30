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

import Lake
open Lake DSL

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require "leanprover" / "doc-gen4" @ git "v4.19.0"

require "leanprover-community" / "batteries" @ git "v4.19.0"

package Cedar

@[default_target]
lean_lib Cedar where
  defaultFacets := #[LeanLib.staticFacet]

@[default_target]
lean_lib SymCC where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib Cedar.SymCC where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib DiffTest where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib UnitTest where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib SymTest where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib Protobuf where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib CedarProto where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib CedarFFI where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib SymFFI where
  defaultFacets := #[LeanLib.staticFacet]

lean_exe CedarUnitTests where
  root := `UnitTest.Main

lean_exe CedarSymTests where
  root := `SymTest.Main

lean_exe Cli where
  root := `Cli.Main

/--
Check that Cedar.Thm imports all top level proofs.

USAGE:
  lake run checkThm
  lake lint
-/
@[lint_driver]
script checkThm do
  let thm ← IO.FS.readFile ⟨"Cedar/Thm.lean"⟩
  let symcc ← IO.FS.readFile ⟨"SymCC.lean"⟩
  let dir ← System.FilePath.readDir ⟨"Cedar/Thm/"⟩
  for entry in dir.toList do
    let fn := entry.fileName
    if fn.endsWith ".lean" then
      let ln := s!"import Cedar.Thm.{fn.dropRight 5}\n"
      if thm.replace ln "" == thm && symcc.replace ln "" == symcc then
        IO.println s!"Neither Cedar.Thm nor SymCC imports Cedar/Thm/{fn}"
        return 1
  return 0
