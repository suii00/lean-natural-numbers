import Lake
open Lake DSL

package «myproject» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.3.0"

lean_lib «MyProject» where
  -- add library configuration options here

lean_lib «TestError» where

@[default_target]
lean_exe «myproject» where
  root := `Main