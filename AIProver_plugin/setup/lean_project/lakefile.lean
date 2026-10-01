
import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.23.0"

require REPL from git
  "https://github.com/leanprover-community/repl.git" @ "2f8073af0a5e3a141fee075652790a2c19132516"

-- CSLib, the Lean library for Computer Science (lambda calculus, combinatory logic, LTS/
-- bisimulation, CCS, linear logic). Pinned to the last commit on Lean v4.23.0: its manifest
-- pins mathlib v4.23.0 (37df177aaa) and batteries d117e2c28c, exactly the revisions above, so
-- it builds against this project's prebuilt oleans without touching them.
require cslib from git
  "https://github.com/leanprover/cslib" @ "cd368e67e7b5cd563be1d7dc47254e9c4d5962cf"

package «TmpProjDir» where
-- add package configuration options here

@[default_target]
lean_lib «TmpProjDir» where
-- add library configuration options here