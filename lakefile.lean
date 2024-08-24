import Lake
open Lake DSL

package «circuits» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.10.0"

lean_lib «Circuits» where
  -- add library configuration options here

@[default_target]
lean_exe «circuits» where
  root := `Main
