import Lake

open Lake DSL

package «ICM2022NumCS97» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

@[default_target]
lean_lib ICM2022NumCS97
