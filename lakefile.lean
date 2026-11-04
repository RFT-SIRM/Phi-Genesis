import Lake
open Lake DSL

package phiGenesis where
  version := v!"0.1.0"
  fixedToolchain := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "6190227179fc32673298fb94e184cdd7fc2581a8"

@[default_target]
lean_lib PhiGenesis where
  roots := #[`PhiGenesis]
