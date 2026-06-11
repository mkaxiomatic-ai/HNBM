import HopfieldNet.ThreeD.BoltzmannLearning.Core
import HopfieldNet.Quiver.NeuralNetwork.TwoState

/-!
## Optional bridge to `HopfieldNet.Quiver.NeuralNetwork.TwoState`

This module connects Bool configurations to TwoState network states and packages
`EnergySpec'` energies as `BM` models. It requires `Physlib`.

Build separately when the TwoState dependency chain is available:
`lake build HopfieldNet.ThreeD.BoltzmannLearning.TwoStateBridge`
-/

namespace NeuralNetwork

namespace ThreeD

namespace BoltzmannLearning

namespace TwoStateBridge

open NeuralNetwork

variable {R : Type} {U : Type} {ζ : Type}

section

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [DecidableEq U]
variable {NN : NeuralNetwork R U ζ} [TwoStateNeuralNetwork NN]

/-- Build a TwoState `NN.State` from a Bool-config by choosing `ζ_pos`/`ζ_neg` pointwise. -/
noncomputable def stateOfConfig (c : BoltzmannLearning.Config U) : NN.State :=
{ act := fun u => cond (c u) (TwoStateNeuralNetwork.ζ_pos (NN := NN)) (TwoStateNeuralNetwork.ζ_neg (NN := NN))
  hp := by
    intro u
    by_cases h : c u
    · simp [h, TwoStateNeuralNetwork.h_pact_pos (NN := NN)]
    · simp [h, TwoStateNeuralNetwork.h_pact_neg (NN := NN)] }

/-- Push an `EnergySpec'` to an energy on Bool-configs via `stateOfConfig` and a ring hom `f`. -/
noncomputable def energyBool
    (E : TwoState.EnergySpec' (R := R) (U := U) (ζ := ζ) NN) (f : R →+* ℝ) (p : _root_.Params NN) :
    BoltzmannLearning.Config U → ℝ :=
  fun c => f (E.E p (stateOfConfig c))

/-- Package the TwoState energy as a `BoltzmannLearning.BM` on Bool-config configurations. -/
noncomputable def bmOfEnergySpec
    (E : TwoState.EnergySpec' (R := R) (U := U) (ζ := ζ) NN) (f : R →+* ℝ) :
    BoltzmannLearning.BM (_root_.Params NN) U :=
{ energy := fun p c => energyBool E f p c }

end

end TwoStateBridge

end BoltzmannLearning

end ThreeD

end NeuralNetwork
