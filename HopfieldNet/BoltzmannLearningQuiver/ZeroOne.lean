/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.Core
import HopfieldNet.Quiver.BM.BoltzmannMachine
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Zero–one Boltzmann machine instance

Primary configuration type: `TwoState.ZeroOne R U` with activations in `{0,1}`.
Sufficient statistics use Ackley-style correlations `a_i a_j` (see `Stat.lean`).
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace ZeroOne

open TwoState HopfieldEnergy HopfieldBoltzmann

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype U] [DecidableEq U] [Nonempty U]

/-- Quiver neural network for `{0,1}` Boltzmann dynamics. -/
abbrev NN (R : Type) (U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U] [Fintype U] [Nonempty U] :=
  TwoState.ZeroOne R U

/-- Legal network state (`a_u ∈ {0,1}`). -/
abbrev State (R : Type) (U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U] [Fintype U] [Nonempty U] :=
  (NN R U).State

/-- External network parameters. -/
abbrev Params (R : Type) (U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U] [Fintype U] [Nonempty U] :=
  _root_.Params (NN R U)

/-- Canonical `{0,1}` Boltzmann Hamiltonian. -/
noncomputable abbrev hamiltonian := HopfieldEnergy.zeroOneHamiltonian (R := R) (U := U)

/-- Energy specification for Gibbs kernels. -/
noncomputable abbrev energySpec := HopfieldEnergy.zeroOneEnergySpec (R := R) (U := U)

/-- Constant all-zero activation profile. -/
noncomputable def defaultState : State R U :=
  { act := fun _ => (0 : R)
    hp := fun _ => Or.inl rfl }

/-- `State R U` is nonempty (all-zero configuration). -/
instance : Nonempty (State R U) := ⟨defaultState⟩
instance : MeasurableSpace (State R U) := ⊤

/-- Decidable equality on `{0,1}` network states (classical). -/
noncomputable instance decidableEqState : DecidableEq (State R U) := Classical.decEq _

end ZeroOne
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
