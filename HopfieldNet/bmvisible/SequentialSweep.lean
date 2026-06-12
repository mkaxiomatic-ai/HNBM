/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.bmvisible.GibbsStationary
import HopfieldNet.Quiver.BM.DetailedBalanceBM
import MCMC.DetailedBalanceGen
import Mathlib.Probability.Kernel.Invariance

/-!
# Sequential Gibbs sweep stationarity (visible/hidden BM)
-/

namespace BMVisible

open MeasureTheory ProbabilityTheory TwoState HopfieldBoltzmann Matrix
open scoped ProbabilityTheory

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable (part : VisibleHiddenPartition U)

private instance singleSiteKernel_isMarkov (u : U) (p : BMParams ℝ U part) (T : Temperature) :
    IsMarkovKernel (singleSiteKernel (NN := NN ℝ U part) (energySpec part) p T u) := by
  refine ⟨?_⟩
  intro s
  unfold singleSiteKernel pmfToKernel
  simpa [Kernel.ofFunOfCountable] using
    (inferInstance : IsProbabilityMeasure
      (TwoState.gibbsUpdate (NN := NN ℝ U part) (RingHom.id ℝ) p T s u).toMeasure)

private instance randomScanGibbsKernel_isMarkov (p : BMParams ℝ U part) (T : Temperature) :
    IsMarkovKernel (randomScanGibbsKernel part p T) := by
  refine ⟨?_⟩
  intro x
  unfold randomScanGibbsKernel randomScanKernel pmfToKernel
  simpa [Kernel.ofFunOfCountable] using
    (inferInstance : IsProbabilityMeasure
      ((PMF.uniformOfFinset (Finset.univ) (by simp)).bind
        (fun u => TwoState.gibbsUpdate (NN := NN ℝ U part) (RingHom.id ℝ) p T x u)).toMeasure)

/-- Sequential sweep kernel: compose single-site kernels in list order (head first). -/
noncomputable def sequentialSweepKernel (p : BMParams ℝ U part) (T : Temperature) :
    List U → Kernel (BMState ℝ U part) (BMState ℝ U part)
  | [] => Kernel.id
  | u :: us =>
      sequentialSweepKernel p T us ∘ₖ singleSiteKernel (NN := NN ℝ U part) (energySpec part) p T u

@[simp] lemma sequentialSweepKernel_nil (p : BMParams ℝ U part) (T : Temperature) :
    sequentialSweepKernel part p T [] = Kernel.id := rfl

@[simp] lemma sequentialSweepKernel_cons (u : U) (us : List U) (p : BMParams ℝ U part) (T : Temperature) :
    sequentialSweepKernel part p T (u :: us) =
      sequentialSweepKernel part p T us ∘ₖ singleSiteKernel (NN := NN ℝ U part) (energySpec part) p T u :=
  rfl

theorem singleSiteKernel_isReversible_negativePhase (u : U) (p : BMParams ℝ U part) (T : Temperature) :
    Kernel.IsReversible (singleSiteKernel (NN := NN ℝ U part) (energySpec part) p T u)
      (negativePhaseMeasure part p T) := by
  dsimp [negativePhaseMeasure]
  convert singleSiteKernel_reversible (NN := NN ℝ U part) (energySpec part) p T u using 1

theorem singleSiteKernel_invariant_negativePhase (u : U) (p : BMParams ℝ U part) (T : Temperature) :
    Kernel.Invariant (singleSiteKernel (NN := NN ℝ U part) (energySpec part) p T u)
      (negativePhaseMeasure part p T) :=
  Kernel.Invariant.of_IsReversible (singleSiteKernel_isReversible_negativePhase part u p T)

theorem sequentialSweepKernel_invariant_negativePhase (order : List U) (p : BMParams ℝ U part)
    (T : Temperature) :
    Kernel.Invariant (sequentialSweepKernel part p T order) (negativePhaseMeasure part p T) := by
  induction order with
  | nil => simp [Kernel.Invariant, sequentialSweepKernel]
  | cons u us ih =>
      have hu := singleSiteKernel_invariant_negativePhase part u p T
      simpa [sequentialSweepKernel] using Kernel.Invariant.comp (hκ := ih) (hη := hu)

theorem negativePhaseMeasure_bind_sequentialSweep (order : List U) (p : BMParams ℝ U part)
    (T : Temperature) :
    (negativePhaseMeasure part p T).bind (sequentialSweepKernel part p T order) =
      negativePhaseMeasure part p T :=
  (sequentialSweepKernel_invariant_negativePhase part order p T).def

theorem gibbsStationaryMeasure_invariant_sequentialSweep (order : List U) (p : BMParams ℝ U part)
    (T : Temperature) :
    Kernel.Invariant (sequentialSweepKernel part p T order) (gibbsStationaryMeasure part p T) := by
  simpa [gibbsStationaryMeasure] using sequentialSweepKernel_invariant_negativePhase part order p T

theorem gibbsStationaryMeasure_invariant_randomScan (p : BMParams ℝ U part) (T : Temperature) :
    Kernel.Invariant (randomScanGibbsKernel part p T) (gibbsStationaryMeasure part p T) := by
  simpa [gibbsStationaryMeasure, randomScanGibbsKernel] using
    Kernel.Invariant.of_IsReversible (randomScanGibbsKernel_isReversible_negativePhase part p T)

theorem same_stationaryMeasure_randomScan_and_sequentialSweep (order : List U) (p : BMParams ℝ U part)
    (T : Temperature) :
    Kernel.Invariant (randomScanGibbsKernel part p T) (negativePhaseMeasure part p T) ∧
      Kernel.Invariant (sequentialSweepKernel part p T order) (negativePhaseMeasure part p T) :=
  ⟨Kernel.Invariant.of_IsReversible (randomScanGibbsKernel_isReversible_negativePhase part p T),
    sequentialSweepKernel_invariant_negativePhase part order p T⟩

end BMVisible

#lint only docBlame
