
import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.23.0"

require REPL from git
  "https://github.com/leanprover-community/repl.git" @ "2f8073af0a5e3a141fee075652790a2c19132516"

package «TmpProjDir» where
-- add package configuration options here

@[default_target]
lean_lib «TmpProjDir» where
-- add library configuration options here