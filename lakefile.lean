import Lake
open Lake DSL

package «myproject» {}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.27.0-rc1"

lean_lib MyProjects {
  srcDir := "src"  -- Changed from 'src' to 'srcDir'
}

@[default_target]
lean_exe myexe {
  root := `MyProjects.Main
  srcDir := "src"  -- Add this line
}
