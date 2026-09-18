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
require "leanprover" / "doc-gen4" @ git "v4.34.0"

require "leanprover-community" / "batteries" @ git "v4.34.0"

package Cedar

@[default_target]
lean_lib Cedar where
  -- Fold only the `LeanParserGenerator` runtime the generated parser/lexer
  -- actually import (`Lexer.*` and `Runtime.*`) into this lib, so they share
  -- one archive the FFI links. Do NOT sweep in the rest of the generator tree
  -- (`LSP`, `Frontend`, `Emit`, `Construct`, `IR`): the LSP server defines a
  -- top-level `main`, and folding it in here makes it the linked binary's
  -- entry point, so the FFI-linked fuzz/test binaries launch the stdio LSP
  -- server and block reading stdin instead of running.
  globs := #[
    Glob.one `Cedar,
    Glob.submodules `LeanParserGenerator.Lexer,
    Glob.submodules `LeanParserGenerator.Runtime
  ]
  defaultFacets := #[LeanLib.staticFacet]

-- The rest of the LeanParserGenerator tooling (grammar frontend, codegen, and
-- the `.lig` LSP server). Not a default target and not linked by the FFI; build
-- it explicitly with `lake build LeanParserGenerator` when working on the
-- generator itself.
lean_lib LeanParserGenerator where
  globs := #[
    Glob.submodules `LeanParserGenerator.Frontend,
    Glob.submodules `LeanParserGenerator.Emit,
    Glob.submodules `LeanParserGenerator.Construct,
    Glob.submodules `LeanParserGenerator.IR,
    Glob.submodules `LeanParserGenerator.LSP
  ]
  defaultFacets := #[LeanLib.staticFacet]

-- Standalone `.lig` language server. Its `main` lives in a dedicated root
-- module so no library that the FFI links can ever contribute a program entry.
lean_exe LigLsp where
  root := `LeanParserGenerator.LSP.Main

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

lean_exe CedarUnitTests where
  root := `UnitTest.Main

lean_exe CedarSymTests where
  root := `SymTest.Main

lean_exe Cli where
  root := `Cli.Main

-- Check that a .lean file imports all files in its corresponding directory
partial def checkThmFile (module : String) (paths : List System.FilePath) : IO Nat := do
  let path := paths.head!
  let dir := path.withExtension ""
  if ← dir.isDir then
    let contents ← paths.mapM IO.FS.readFile
    let mod_files ← dir.readDir
    let mut exitCode := 0

    for file in mod_files.toList do
      let file_name := file.fileName
      if file_name.endsWith ".lean" then
        let subModule := s!"{module}.{file_name.dropEnd 5}"
        let expectedImport := s!"import {subModule}\n"
        if contents.all λ content => (content.replace expectedImport "" == content) then
          IO.println s!"{path} missing import: {expectedImport}"
          exitCode := 1
        let subExitCode ← checkThmFile subModule [dir / file_name]
        if subExitCode != 0 then
          exitCode := subExitCode

    return exitCode
  else
    return 0

/--
Check that Cedar.Thm imports all top level proofs recursively.

USAGE:
  lake run checkThm
  lake lint
-/
@[lint_driver]
script checkThm do
  let exitCode ← checkThmFile "Cedar.Thm" [⟨"Cedar/Thm.lean"⟩, ⟨"SymCC.lean"⟩]
  return ⟨exitCode⟩
