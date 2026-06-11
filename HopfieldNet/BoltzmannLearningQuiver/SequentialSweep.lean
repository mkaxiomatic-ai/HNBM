/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.GibbsStationary
import HopfieldNet.Quiver.BM.DetailedBalanceBM
import MCMC.DetailedBalanceGen
import Mathlib.Probability.Kernel.Invariance

/-!
# Sequential Gibbs sweep stationarity

Sequential sweeps preserve the Boltzmann negative phase.
-/

namespace NeuralNetwork

namespace BoltzmannLearningQuiver

namespace SymmetricBinary

open MeasureTheory ProbabilityTheory TwoState HopfieldBoltzmann Matrix
open scoped ProbabilityTheory

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

private instance singleSiteKernel_isMarkov (u : U) (p : Params ℝ U) (T : Temperature) :
    IsMarkovKernel (singleSiteKernel (NN := NN ℝ U) energySpec p T u) := by
  refine ⟨?_⟩
  intro s
  unfold singleSiteKernel pmfToKernel
  simpa [Kernel.ofFunOfCountable] using
    (inferInstance : IsProbabilityMeasure
      (TwoState.gibbsUpdate (NN := NN ℝ U) (RingHom.id ℝ) p T s u).toMeasure)

private instance randomScanGibbsKernel_isMarkov (p : Params ℝ U) (T : Temperature) :
    IsMarkovKernel (randomScanGibbsKernel p T) := by
  refine ⟨?_⟩
  intro x
  unfold randomScanGibbsKernel randomScanKernel pmfToKernel
  simpa [Kernel.ofFunOfCountable] using
    (inferInstance : IsProbabilityMeasure
      ((PMF.uniformOfFinset (Finset.univ) (by simp)).bind
        (fun u => TwoState.gibbsUpdate (NN := NN ℝ U) (RingHom.id ℝ) p T x u)).toMeasure)

/-!
### Sequential sweep kernel
-/

/-- Sequential sweep kernel: compose single-site kernels in list order (head first). -/
noncomputable def sequentialSweepKernel (p : Params ℝ U) (T : Temperature) :
    List U → Kernel (State ℝ U) (State ℝ U)
  | [] => Kernel.id
  | u :: us =>
      sequentialSweepKernel p T us ∘ₖ singleSiteKernel (NN := NN ℝ U) energySpec p T u

/-- Simp: empty sweep is the identity kernel. -/
@[simp] lemma sequentialSweepKernel_nil (p : Params ℝ U) (T : Temperature) :
    sequentialSweepKernel p T [] = Kernel.id :=
  rfl

/-- Simp: cons extends the sweep by composing one more single-site kernel. -/
@[simp] lemma sequentialSweepKernel_cons (u : U) (us : List U) (p : Params ℝ U) (T : Temperature) :
    sequentialSweepKernel p T (u :: us) =
      sequentialSweepKernel p T us ∘ₖ singleSiteKernel (NN := NN ℝ U) energySpec p T u :=
  rfl

-- Stationarity

/-- Single-site Gibbs update is reversible w.r.t. the learning negative phase. -/
theorem singleSiteKernel_isReversible_negativePhase (u : U) (T : Temperature) (p : Params ℝ U) :
    Kernel.IsReversible (singleSiteKernel (NN := NN ℝ U) energySpec p T u)
      (negativePhaseMeasure T p) := by
  dsimp [negativePhaseMeasure]
  convert singleSiteKernel_reversible (NN := NN ℝ U) energySpec p T u using 1

/-- Single-site Gibbs update leaves the negative phase invariant. -/
theorem singleSiteKernel_invariant_negativePhase (u : U) (T : Temperature) (p : Params ℝ U) :
    Kernel.Invariant (singleSiteKernel (NN := NN ℝ U) energySpec p T u)
      (negativePhaseMeasure T p) :=
  Kernel.Invariant.of_IsReversible (singleSiteKernel_isReversible_negativePhase u T p)

/-- **Main result:** every sequential Gibbs sweep preserves the Boltzmann negative phase. -/
theorem sequentialSweepKernel_invariant_negativePhase (order : List U) (T : Temperature)
    (p : Params ℝ U) :
    Kernel.Invariant (sequentialSweepKernel p T order) (negativePhaseMeasure T p) := by
  induction order with
  | nil =>
      simp [Kernel.Invariant, sequentialSweepKernel]
  | cons u us ih =>
      have hu := singleSiteKernel_invariant_negativePhase u T p
      simpa [sequentialSweepKernel] using
        Kernel.Invariant.comp (hκ := ih) (hη := hu)

/-- Applying a sweep kernel to the equilibrium measure returns it. -/
theorem negativePhaseMeasure_bind_sequentialSweep (order : List U) (T : Temperature)
    (p : Params ℝ U) :
    (negativePhaseMeasure T p).bind (sequentialSweepKernel p T order) =
      negativePhaseMeasure T p :=
  (sequentialSweepKernel_invariant_negativePhase order T p).def

/-- Sequential Gibbs dynamics leave `gibbsStationaryMeasure` invariant. -/
theorem gibbsStationaryMeasure_invariant_sequentialSweep (order : List U) (T : Temperature)
    (p : Params ℝ U) :
    Kernel.Invariant (sequentialSweepKernel p T order) (gibbsStationaryMeasure T p) := by
  simpa [gibbsStationaryMeasure] using
    sequentialSweepKernel_invariant_negativePhase order T p

/-- Random-scan Gibbs dynamics leave `gibbsStationaryMeasure` invariant. -/
theorem gibbsStationaryMeasure_invariant_randomScan (T : Temperature) (p : Params ℝ U) :
    Kernel.Invariant (randomScanGibbsKernel p T) (gibbsStationaryMeasure T p) := by
  simpa [gibbsStationaryMeasure, randomScanGibbsKernel] using
    Kernel.Invariant.of_IsReversible (randomScanGibbsKernel_isReversible_negativePhase T p)

/-- Both samplers have the Boltzmann learning negative phase as a stationary measure. -/
theorem same_stationaryMeasure_randomScan_and_sequentialSweep (order : List U)
    (T : Temperature) (p : Params ℝ U) :
    Kernel.Invariant (randomScanGibbsKernel p T) (negativePhaseMeasure T p) ∧
      Kernel.Invariant (sequentialSweepKernel p T order) (negativePhaseMeasure T p) :=
  ⟨Kernel.Invariant.of_IsReversible (randomScanGibbsKernel_isReversible_negativePhase T p),
    sequentialSweepKernel_invariant_negativePhase order T p⟩

end SymmetricBinary

end BoltzmannLearningQuiver

end NeuralNetwork

#lint only docBlame docBlameThm
