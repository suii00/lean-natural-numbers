import Lake
open Lake DSL

package myproject

require mathlib from git
 "https://github.com/leanprover-community/mathlib4" @ "v4.22.0"


@[default_target]
lean_lib MyProofs where
  srcDir := "src"