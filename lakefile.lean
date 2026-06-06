import Lake
open Lake DSL

package «qseries_formalization» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.27.0"

@[default_target]
lean_lib QseriesFormalization where

lean_exe qseries_formalization where
  root := `Main
