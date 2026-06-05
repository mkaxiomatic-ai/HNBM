/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.Learning
import HopfieldNet.BoltzmannLearningQuiver.SymmetricBinary

/-!
## Positive and negative phases on Quiver states

The **negative phase** is expressed through the Boltzmann probabilities from
`HopfieldBoltzmann.P` (canonical ensemble on `NN.State`).

The **positive phase** (clamp to data, then equilibrate) is still abstract: it will be
instantiated with `TwoState.gibbsUpdate` / clamping kernels in a later module.
-/

namespace NeuralNetwork

namespace BoltzmannLearningQuiver

namespace SymmetricBinary

open ThreeD.BoltzmannLearning VectorGibbs
open TwoState HopfieldBoltzmann HopfieldEnergy

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Boltzmann probability `P_θ,T(s)` for a Quiver state (from the canonical ensemble). -/
noncomputable def modelProbability (T : Temperature) (p : Params ℝ U) (s : State ℝ U) : ℝ :=
  HopfieldBoltzmann.P (NN := NN ℝ U) (spec := energySpec) p T s

/-- Finite-state expectation `E_{s ∼ P(·|θ,T)}[stat s]` (coordinate-wise). -/
noncomputable def modelExpectationStat (_T : Temperature) (p : Params ℝ U) : Θ U :=
  expectation (X := State ℝ U) (Θ := Θ U) stat (thetaFromParams p)

/-- Coordinate-wise learning direction for a single data state `s_data`. -/
noncomputable def learningDirection (T : Temperature) (p : Params ℝ U) (s_data : State ℝ U) : Θ U :=
  stat s_data - modelExpectationStat T p

/-- Single-sample gradient direction at `p` agrees with `learningDirection` (any temperature). -/
theorem learningDirection_eq_negLogLik_gradient (T : Temperature) (p : Params ℝ U) (s_data : State ℝ U) :
    learningDirection T p s_data =
      stat s_data - expectation (X := State ℝ U) (Θ := Θ U) stat (thetaFromParams p) := by
  rfl

end SymmetricBinary

end BoltzmannLearningQuiver

end NeuralNetwork
