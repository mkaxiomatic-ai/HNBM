import Lake
open Lake DSL

package «HopfieldNet» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

@[default_target]
lean_lib «HopfieldNet» where
  -- add any library configuration options here

lean_lib QUBO where
  globs := #[.submodules `HopfieldNet.QUBO]

lean_lib CNS where
  -- Collaborative neurodynamic Sudoku (Li & Wang, ICIST 2022).
  -- Deliberately Mathlib-free below `CNS.Spec`, so the data and execution layers
  -- rebuild in seconds.
  globs := #[.submodules `HopfieldNet.CNS]

/-- Reproduce the paper's tables: `lake exe cns table1`. -/
lean_exe cns where
  root := `HopfieldNet.CNS.Main

lean_lib CNSDemo where
  -- The `#animate` demos. A target of its own, and deliberately not a default target:
  -- the animation frames are computed during elaboration, so building this runs the solver.

lean_lib MCMC where
  -- Builds the `MCMC.*` modules living under the top-level `MCMC/` directory.

lean_lib PF where
  -- Builds the `PF.*` modules living under the top-level `PF/` directory.
  -- There is no `PF.lean` root module, so glob the submodules directly.
  globs := #[.submodules `PF]

-- lean_lib GibbsMeasure where
--   -- Builds the `GibbsMeasure.*` modules living under the top-level `GibbsMeasure/` directory.

-- lean_lib ThreeD where
--   -- Builds the `GibbsMeasure.*` modules living under the top-level `GibbsMeasure/` directory.

--lean_lib Optlib where

require «physlib» from git
  "https://github.com/leanprover-community/physlib.git"

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

--meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.2"
