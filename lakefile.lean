import Lake
open Lake DSL

package phiGenesis where
  version := v!"0.1.0"
  fixedToolchain := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "v4.33.1"

@[default_target]
lean_lib PhiGenesis where
  roots := #[`PhiGenesis]
