import Lake
open Lake DSL

package «myproject» {}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.22.0"

lean_lib MyProofs {
  srcDir := "src"  -- Changed from 'src' to 'srcDir'
}

@[default_target]
lean_exe myexe {
  root := `MyProofs.Main
  srcDir := "src"  -- Add this line
}