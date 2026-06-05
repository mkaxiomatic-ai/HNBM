/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.Core
import HopfieldNet.Quiver.BM.BoltzmannMachine

/-!
## SymmetricBinary as the primary Quiver BM instance

All development in this folder specializes to `TwoState.SymmetricBinary R U`, the standard
`{±1}` Hopfield / Boltzmann machine from the Quiver library.
-/

namespace NeuralNetwork

namespace BoltzmannLearningQuiver

namespace SymmetricBinary

open TwoState HopfieldEnergy HopfieldBoltzmann

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype U] [DecidableEq U] [Nonempty U]

/-- The Quiver neural network for standard binary Hopfield / BM dynamics. -/
abbrev NN (R : Type) (U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U] [Fintype U] [Nonempty U] :=
  TwoState.SymmetricBinary R U

/-- A legal network state (activation `U → ζ` with `{±1}` predicate). -/
abbrev State (R : Type) (U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U] [Fintype U] [Nonempty U] :=
  (NN R U).State

/-- External parameters (weight matrix, thresholds, validity proofs). -/
abbrev Params (R : Type) (U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U] [Fintype U] [Nonempty U] :=
  _root_.Params (NN R U)

/-- Canonical Hopfield Hamiltonian from the Quiver BM library. -/
noncomputable abbrev hamiltonian := HopfieldEnergy.hamiltonian (R := R) (U := U)

/-- Energy specification used by Gibbs kernels and the canonical ensemble. -/
noncomputable abbrev energySpec := HopfieldEnergy.symmetricBinaryEnergySpec (R := R) (U := U)

/-- Constant `+1` activation profile (always a legal `{±1}` state). -/
noncomputable def defaultState : State R U :=
  { act := fun _ => (1 : R)
    hp := fun _ => Or.inl rfl }

instance : Nonempty (State R U) :=
  ⟨defaultState⟩

end SymmetricBinary

end BoltzmannLearningQuiver

end NeuralNetwork
