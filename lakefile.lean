-- SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
-- SPDX-License-Identifier: Apache-2.0
import Lake
open Lake DSL
open System (FilePath)

require "leanprover-community" / "batteries" @ git "v4.35.0"

package «grounding» where
  precompileModules := true

def nativeBuildDir (pkg : Package) : FilePath :=
  pkg.buildDir / "native"

def cmakeBuildType : BuildType → String
  | .debug => "Debug"
  | .relWithDebInfo => "RelWithDebInfo"
  | .minSizeRel => "MinSizeRel"
  | .release => "Release"

/-- Inputs whose changes rebuild the native library. -/
def nativeInputs (pkg : NPackage __name__) : FetchM (Job Unit) := do
  let isSrc (p : FilePath) :=
    p.extension ∈ [some "cpp", some "cc", some "h", some "hpp", some "txt"]
  let ours ← inputDir (pkg.dir / "native") (text := true) isSrc
  let frontend ← inputDir (pkg.dir / "third_party" / "sv-elab" / "src") (text := true) isSrc
  return ours.mix frontend

target groundingNative (pkg : NPackage __name__) : FilePath := do
  let inputs ← nativeInputs pkg
  let buildDir := nativeBuildDir pkg
  let lib := buildDir / nameToStaticLib "grounding_sv"
  let leanInclude ← getLeanIncludeDir
  inputs.mapM fun _ => do
    addPureTrace (cmakeBuildType pkg.buildType) "cmakeBuildType"
    buildFileUnlessUpToDate' lib do
      IO.FS.createDirAll buildDir
      let jobs := (← IO.getEnv "GROUNDING_NATIVE_JOBS").getD "2"
      proc {
        cmd := "cmake"
        args := #["-S", (pkg.dir / "native").toString, "-B", buildDir.toString,
                  s!"-DCMAKE_BUILD_TYPE={cmakeBuildType pkg.buildType}",
                  s!"-DLEAN_INCLUDE_DIR={leanInclude}"]
      }
      proc {
        cmd := "cmake"
        args := #["--build", buildDir.toString, "--target", "grounding_sv", "-j", jobs]
      }
    return lib

@[default_target]
lean_lib Grounding where
  roots := #[`Grounding]
  needs := #[`@/groundingNative]
  moreLinkObjs := #[`@/groundingNative]

@[test_driver]
lean_exe tests where
  root := `Tests
