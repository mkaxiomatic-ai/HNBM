/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.bmvisible.Phases
import HopfieldNet.Quiver.BM.Ergodicity

/-!
# Gibbs stationary measure = BM negative phase (visible/hidden)
-/

namespace BMVisible

open MeasureTheory ProbabilityTheory TwoState HopfieldBoltzmann Matrix

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable (part : VisibleHiddenPartition U)

/-- Random-scan Gibbs kernel on visible/hidden `{0,1}` states. -/
noncomputable def randomScanGibbsKernel (p : BMParams ℝ U part) (T : Temperature) :
    Kernel (BMState ℝ U part) (BMState ℝ U part) :=
  randomScanKernel (NN := NN ℝ U part) (energySpec part) p T

/-- Alias for `negativePhaseMeasure`. -/
noncomputable abbrev gibbsStationaryMeasure (p : BMParams ℝ U part) (T : Temperature) :
    Measure (BMState ℝ U part) :=
  negativePhaseMeasure part p T

/-- Random-scan Gibbs kernel is reversible w.r.t. the negative phase. -/
theorem randomScanGibbsKernel_isReversible_negativePhase (p : BMParams ℝ U part) (T : Temperature) :
    Kernel.IsReversible (randomScanGibbsKernel part p T) (negativePhaseMeasure part p T) := by
  dsimp [randomScanGibbsKernel, negativePhaseMeasure]
  exact randomScanKernel_reversible (NN := NN ℝ U part) (energySpec part) p T

/-- Random-scan Gibbs ergodicity on the visible/hidden negative phase. -/
theorem negativePhaseMeasure_is_gibbs_stationary (p : BMParams ℝ U part) (T : Temperature) :
    Kernel.IsReversible (randomScanGibbsKernel part p T) (negativePhaseMeasure part p T) ∧
    (∀ s, 0 < RScol (NN := NN ℝ U part) (energySpec part) p T s s) ∧
    Matrix.IsIrreducible (RScol (NN := NN ℝ U part) (energySpec part) p T) ∧
    ∃! v : stdSimplex ℝ (BMState ℝ U part),
      mulVec (RScol (NN := NN ℝ U part) (energySpec part) p T) v.val = v.val := by
  dsimp [randomScanGibbsKernel, negativePhaseMeasure]
  exact randomScan_ergodicUniqueInvariant (NN := NN ℝ U part) (energySpec part) p T

end BMVisible

#lint only docBlame
