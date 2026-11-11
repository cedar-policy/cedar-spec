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
require "leanprover" / "doc-gen4" @ git "v4.35.0"

require "leanprover-community" / "batteries" @ git "v4.35.0"

-- Specimen derives the relational spec's generators (`CedarGen`), against Basalt
require specimen from git "https://github.com/strata-org/specimen" @ "163729a3fbaebb673bea391a542a1801610bf39c"

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

/-- `--load-dynlib` for the compiled libraries of Specimen, Basalt and their dependencies that have
been built (their `:dynlib` facets), so that the derivations and proofs run Specimen's and
Basalt's tactics compiled; a library not built is left out, and its code is interpreted (the same
results, more slowly). In dependency order. -/
def nativeLibs : Array String := run_io do
  let libs : Array String := #[
    ".lake/packages/batteries/.lake/build/lib/libbatteries_Batteries.so",
    ".lake/packages/Qq/.lake/build/lib/libQq_Qq.so",
    ".lake/packages/aesop/.lake/build/lib/libaesop_Aesop.so",
    ".lake/packages/proofwidgets/.lake/build/lib/libproofwidgets_ProofWidgets.so",
    ".lake/packages/importGraph/.lake/build/lib/libimportGraph_ImportGraph.so",
    ".lake/packages/LeanSearchClient/.lake/build/lib/libLeanSearchClient_LeanSearchClient.so",
    ".lake/packages/plausible/.lake/build/lib/libplausible_Plausible.so",
    ".lake/packages/mathlib/.lake/build/lib/libmathlib_Mathlib.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_LazyList.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Utils.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Enumerators.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_GeneratorCombinators.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_TSyntaxCombinators.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Idents.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_UnificationMonad.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Score.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Schedules.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_WorkerRegistry.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Debug.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_MakeConstrainedProducerInstance.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Scoring.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_LazyRoseTree.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_SearchTree.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_DeriveSchedules.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_ArbitrarySizedSuchThat.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_DecOpt.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_MExp.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_PatternCoverage.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Rejections.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_DeriveFloors.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_DeriveConstrainedProducer.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_DeriveChecker.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_EnumeratorCombinators.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_DeriveEnum.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_DeriveArbitrary.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_ScoringInversion.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_TheoremChecker.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Tactic_Schedule.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Tactic_TestLoop.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Tactic_Shrink.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Tactic_Widget.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Tactic.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_RandomChoice.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Enum_Fail.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Gen.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Enum_ExceptT.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_PlausibleGen.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Order.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Combinators.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Enum_Finite.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Sized.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Enum_Backtrack.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Enum_Pick.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Enum_BacktrackWith.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Enum_Search.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_OptionT.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_BasaltClasses.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Sampler.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_BasaltBridge.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_SamplerAgreement.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_DeriveBasaltArbitrary.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Basalt.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_Semantics.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_GenRel_Basic.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Obs_Basic.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Walk_Attr.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_GenRel.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Enum_Laws_GenRel.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Obs_Spec.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Obs_Combinators.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Obs_Ordered.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Obs_Presentation.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_SPMF_Basic.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_SPMF_Expect_Basic.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_SPMF_Expect_Obs.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_SPMF_Support.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_SPMF_Cost.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_SPMF_CostErasure.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_SPMF_Mass.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_SPMF_Termination.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Laws.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Enum_Laws_Basic.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Enum_Laws_Fail.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Enum_Laws_Backtrack.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Enum_Laws_BacktrackWith.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_GenInterpSPMF.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_SizeMeasure.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Walk_Sound.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Walk_Match.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Walk_Names.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Walk_Basic.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Walk_Entry.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_WalkSGen.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Walk_Complete.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_LeafSPMF.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_SuccObs.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_ReachObs.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_LawClasses.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_CheckHyps.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_ParallelBlock.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_StepOf.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_SoundOf.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Enum_Laws_Search.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_SearchFinds.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_SearchHits.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_LazyListLemmas.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_Combinators.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_CheckComplete.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_ReachClose.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_LeafComplete.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_SplitLaws.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_FloorLaws.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_EnumSoundOf.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_EnumCompleteOf.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_CheckSoundOf.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_LeafLaws.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_CompleteOf.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_GenExpectSPMF.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_CondMean.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_FloorOf.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_SureLaws.so",
    ".lake/packages/basalt/.lake/build/lib/lean/basalt_Basalt_Walk_Average.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_WalkSGenExpect.so",
    ".lake/packages/specimen/.lake/build/lib/lean/specimen_Specimen_Correctness_WalkSGenSelf.so"]
  let mut args := #[]
  for l in libs do
    let p : System.FilePath := __dir__ / l
    if ← p.pathExists then args := args.push s!"--load-dynlib={p}"
  return args

-- Generators for the relational spec, derived with Specimen. Not a default target.
-- The Basalt emission flag has to be set for the whole library (Specimen's
-- Docs/Specimen-Basalt-port.md, section 7.1); `weak.` because not every module imports Specimen.
lean_lib CedarGen where
  leanOptions := #[⟨`weak.specimen.emitBasalt, true⟩]
  moreLeanArgs := nativeLibs


-- The proofs that the expression generators are sound and complete (`CedarGenProof.ExprGen`).
lean_lib CedarGenProof where
  roots := #[`CedarGenProof.ExprGen, `CedarGenProof.ExprGen.Setup, `CedarGenProof.ExprGen.Sound,
    `CedarGenProof.ExprGen.Parts]
  moreLeanArgs := nativeLibs

-- The large components' parts, checked 24 at once, with 8 threads each.
lean_lib CedarGenProofParts where
  globs := #[.submodules `CedarGenProof.ExprGen.Parts]
  moreLeanArgs := nativeLibs.push "-j8"

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
        let expectedImports := [s!"import {subModule}\n", s!"import all {subModule}\n"]
        if contents.all λ content =>
            expectedImports.all λ expected => content.replace expected "" == content
        then
          IO.println s!"{path} missing import: import {subModule}"
          exitCode := 1
        let subExitCode ← checkThmFile subModule (dir / file_name :: paths)
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
