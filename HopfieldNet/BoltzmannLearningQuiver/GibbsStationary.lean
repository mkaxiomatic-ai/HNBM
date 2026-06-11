/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.SymmetricBinary
import HopfieldNet.BoltzmannLearningQuiver.Phases
import HopfieldNet.Quiver.BM.Ergodicity

/-!
# Gibbs stationary measure = BM negative phase

Random-scan Gibbs ergodicity in learning-layer notation.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace SymmetricBinary

open MeasureTheory ProbabilityTheory TwoState HopfieldBoltzmann Matrix

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Random-scan Gibbs kernel on quiver `{±1}` states. -/
noncomputable def randomScanGibbsKernel (p : Params ℝ U) (T : Temperature) : Kernel (State ℝ U) (State ℝ U) :=
  randomScanKernel (NN := NN ℝ U) energySpec p T

/-- Alias for `negativePhaseMeasure`. -/
noncomputable abbrev gibbsStationaryMeasure (T : Temperature) (p : Params ℝ U) : Measure (State ℝ U) :=
  negativePhaseMeasure T p

/-- Random-scan Gibbs kernel is reversible w.r.t. the negative phase. -/
theorem randomScanGibbsKernel_isReversible_negativePhase (T : Temperature) (p : Params ℝ U) :
    Kernel.IsReversible (randomScanGibbsKernel p T) (negativePhaseMeasure T p) := by
  dsimp [randomScanGibbsKernel, negativePhaseMeasure]
  exact randomScanKernel_reversible (NN := NN ℝ U) energySpec p T

/-- Random-scan Gibbs ergodicity package in learning-layer notation. -/
theorem negativePhaseMeasure_is_gibbs_stationary (T : Temperature) (p : Params ℝ U) :
    Kernel.IsReversible (randomScanGibbsKernel p T) (negativePhaseMeasure T p) ∧
    (∀ s, 0 < RScol (NN := NN ℝ U) energySpec p T s s) ∧
    Matrix.IsIrreducible (RScol (NN := NN ℝ U) energySpec p T) ∧
    ∃! v : stdSimplex ℝ (State ℝ U),
      mulVec (RScol (NN := NN ℝ U) energySpec p T) v.val = v.val := by
  dsimp [randomScanGibbsKernel, negativePhaseMeasure]
  exact randomScan_ergodicUniqueInvariant (NN := NN ℝ U) energySpec p T

end SymmetricBinary
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
