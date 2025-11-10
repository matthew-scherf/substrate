import Lake
open Lake DSL

package «SubstrateTheory» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib SubstrateTheory

lean_exe Substrate where
  root := `Main
