/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.Core
import HopfieldNet.Quiver.BM.BoltzmannMachine
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Symmetric binary Hopfield / BM instance

Primary configuration type: `TwoState.SymmetricBinary R U` with activations in `{±1}`.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace SymmetricBinary

open TwoState HopfieldEnergy HopfieldBoltzmann

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype U] [DecidableEq U] [Nonempty U]

/-- Quiver neural network for symmetric-binary Hopfield dynamics. -/
abbrev NN (R : Type) (U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U] [Fintype U] [Nonempty U] :=
  TwoState.SymmetricBinary R U

/-- Legal network state. -/
abbrev State (R : Type) (U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U] [Fintype U] [Nonempty U] :=
  (NN R U).State

/-- External network parameters. -/
abbrev Params (R : Type) (U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U] [Fintype U] [Nonempty U] :=
  _root_.Params (NN R U)

/-- Canonical Hopfield Hamiltonian. -/
noncomputable abbrev hamiltonian := HopfieldEnergy.hamiltonian (R := R) (U := U)

/-- Energy specification for Gibbs kernels. -/
noncomputable abbrev energySpec := HopfieldEnergy.symmetricBinaryEnergySpec (R := R) (U := U)

/-- Constant `+1` activation profile. -/
noncomputable def defaultState : State R U :=
  { act := fun _ => (1 : R)
    hp := fun _ => Or.inl rfl }

/-- `State R U` is nonempty. -/
instance : Nonempty (State R U) := ⟨defaultState⟩
instance : MeasurableSpace (State R U) := ⊤
noncomputable instance decidableEqState : DecidableEq (State R U) := Classical.decEq _

end SymmetricBinary
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
