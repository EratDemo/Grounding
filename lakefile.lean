import Lake
open Lake DSL
open System (FilePath)

require "leanprover-community" / "batteries" @ git "v4.35.0"

package «grounding» where
  precompileModules := true
