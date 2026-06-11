/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.LearningRule
import HopfieldNet.BoltzmannLearningQuiver.Dynamics

/-!
# Contrastive divergence (CD-k) definitions

CD-k approximates the negative phase by `k` sequential Gibbs sweeps from clamped data.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace SymmetricBinary

open MeasureTheory TwoState

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- One CD step: push a distribution through one sequential Gibbs sweep. -/
noncomputable def cdStepPMF (order : List U) (p : Params ℝ U) (T : Temperature)
    (μ : PMF (State ℝ U)) : PMF (State ℝ U) :=
  μ.bind fun s => gibbsSweep order p T (RingHom.id ℝ) s

/-- CD-k state distribution from Dirac at `s_data`. -/
noncomputable def cdNegativePMF (k : ℕ) (order : List U) (p : Params ℝ U) (T : Temperature)
    (s_data : State ℝ U) : PMF (State ℝ U) :=
  Nat.rec (PMF.pure s_data) (fun _ μ => cdStepPMF order p T μ) k

/-- CD-k negative phase as a measure. -/
noncomputable def cdNegativePhaseMeasure (k : ℕ) (order : List U) (p : Params ℝ U) (T : Temperature)
    (s_data : State ℝ U) : Measure (State ℝ U) :=
  (cdNegativePMF k order p T s_data).toMeasure

/-- CD-k learning direction. -/
noncomputable def cdLearningDirection (k : ℕ) (order : List U) (T : Temperature) (p : Params ℝ U)
    (s_data : State ℝ U) : Θ U :=
  learningRule.updateDir (positivePhaseAtData s_data)
    (cdNegativePhaseMeasure k order p T s_data)

end SymmetricBinary
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
