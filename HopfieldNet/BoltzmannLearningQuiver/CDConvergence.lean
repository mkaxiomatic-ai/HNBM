/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.DynamicsEquivalence
import HopfieldNet.BoltzmannLearningQuiver.ContrastiveDivergence
import HopfieldNet.BoltzmannLearningQuiver.SequentialSweepUnique
import HopfieldNet.BoltzmannLearningQuiver.Phases
import HopfieldNet.BoltzmannLearningQuiver.LearningRule
import HopfieldNet.Quiver.NeuralNetwork.toCanonicalEnsemble
import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
import MCMC.Convergence
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Constructions

/-!
# CD-k convergence under a full sequential sweep

With `IsFullSweep order`, CD-k learning direction → exact learning direction as `k → ∞`.
-/

namespace NeuralNetwork

namespace BoltzmannLearningQuiver

namespace ZeroOne

open Classical MeasureTheory ProbabilityTheory Filter Topology CanonicalEnsemble Finset
open HopfieldBoltzmann
open scoped ProbabilityTheory ENNReal BigOperators Temperature CanonicalEnsemble

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

local notation "State" => State ℝ U

private lemma distributionAtTime_dirac_tendsto (order : List U) (h : IsFullSweep order)
    (T : Temperature) (p : Params ℝ U) (s₀ : State) :
    Tendsto (distributionAtTime (sweepRowMatrix p T order) (diracSimplex s₀)) atTop
      (𝓝 (negativePhaseVec T p).val) := by
  haveI := sweepRowMatrix_isMCMC order h T p
  exact distribution_converges_to_stationarity (sweepRowMatrix p T order) (negativePhaseVec T p)
    inferInstance (diracSimplex s₀)

/-- CD-k PMF at `t` converges to Boltzmann weight `(negativePhaseVec T p).val t`. -/
theorem cdNegativePMF_tendsto_negativePhase (order : List U) (h : IsFullSweep order)
    (T : Temperature) (p : Params ℝ U) (s₀ t : State) :
    Tendsto (fun k => cdNegativePMF k order p T s₀ t) atTop
      (𝓝 (ENNReal.ofReal ((negativePhaseVec T p).val t))) := by
  have hdist := distributionAtTime_dirac_tendsto order h T p s₀
  have ht := tendsto_pi_nhds.mp hdist t
  have hnn : ∀ k, 0 ≤ distributionAtTime (sweepRowMatrix p T order) (diracSimplex s₀) k t :=
    fun k => distributionAtTime_dirac_nonneg order p T s₀ k t
  simpa [cdNegativePMF_apply_eq_distributionAtTime] using ENNReal.tendsto_ofReal ht

/-- CD-k negative phase assigns vanishing mass to any state whose mass vanishes at equilibrium. -/
theorem cdNegativePMF_tendsto_zero_of_model_zero (order : List U) (h : IsFullSweep order)
    (T : Temperature) (p : Params ℝ U) (s₀ t : State)
    (hzero : (negativePhaseVec T p).val t = 0) :
    Tendsto (fun k => cdNegativePMF k order p T s₀ t) atTop (𝓝 0) := by
  have hlim := cdNegativePMF_tendsto_negativePhase order h T p s₀ t
  simpa [hzero, ENNReal.ofReal_zero] using hlim

private lemma cdExpectationStatCoord_eq_sum (k : ℕ) (order : List U) (p : Params ℝ U)
    (T : Temperature) (s₀ : State) (i : I U) :
    BM.expectation (cdNegativePhaseMeasure k order p T s₀) (statCoord i) =
      ∑ t, distributionAtTime (sweepRowMatrix p T order) (diracSimplex s₀) k t * statCoord i t := by
  simp [cdNegativePhaseMeasure, BM.expectation, statCoord, MeasureTheory.integral_fintype,
    cdNegativePMF_apply_eq_distributionAtTime, measureReal_def, ENNReal.toReal_ofReal, smul_eq_mul,
    distributionAtTime_dirac_nonneg order p T s₀]

private lemma modelExpectationStatCoord_eq_sum (T : Temperature) (p : Params ℝ U) (i : I U) :
    BM.expectation (negativePhaseMeasure T p) (statCoord i) =
      ∑ t, (negativePhaseVec T p).val t * statCoord i t := by
  haveI : (CEparams (NN := NN ℝ U) (spec := energySpec) p).IsFinite := inferInstance
  simp [BM.expectation, negativePhaseMeasure, statCoord, MeasureTheory.integral_fintype,
    measureReal_def, negativePhaseVec, πBoltzVec, μBoltz,
    boltzmann_singleton_eval (NN := NN ℝ U) energySpec p T, smul_eq_mul]
/-- CD-k negative-phase statistic converges to Boltzmann `E[stat]`. -/
theorem cdExpectationStat_tendsto_modelExpectationStat (order : List U) (h : IsFullSweep order)
    (T : Temperature) (p : Params ℝ U) (s₀ : State) (i : I U) :
    Tendsto (fun k => BM.expectation (cdNegativePhaseMeasure k order p T s₀) (statCoord i)) atTop
      (𝓝 (BM.expectation (negativePhaseMeasure T p) (statCoord i))) := by
  have hdist := distributionAtTime_dirac_tendsto order h T p s₀
  rw [modelExpectationStatCoord_eq_sum]
  have hT := tendsto_finsetSum Finset.univ fun t _ =>
    (tendsto_pi_nhds.mp hdist t).mul_const (statCoord i t)
  exact hT.congr' (Eventually.of_forall fun k => (cdExpectationStatCoord_eq_sum k order p T s₀ i).symm)

private lemma tendsto_euclidean_of_forall_coord {ι : Type*} [Fintype ι] [Nonempty ι]
    {f : ℕ → EuclideanSpace ℝ ι} {l : EuclideanSpace ℝ ι}
    (h : ∀ i, Tendsto (fun k => (f k) i) atTop (𝓝 (l i))) :
    Tendsto f atTop (𝓝 l) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set n : ℕ := Fintype.card ι
  have hn : 0 < n := Fintype.card_pos
  set bound : ℝ := ε / Real.sqrt n
  have hbound : 0 < bound := div_pos hε (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hcoord_bound : ∀ i, ∃ N, ∀ k ≥ N, dist ((f k) i) (l i) < bound :=
    fun i => Metric.tendsto_atTop.mp (h i) bound hbound
  set N := Finset.sup' Finset.univ Finset.univ_nonempty
    (fun i => Classical.choose (hcoord_bound i))
  refine ⟨N, fun k hk => ?_⟩
  have hcoord : ∀ i, dist ((f k) i) (l i) < bound := fun i =>
    Classical.choose_spec (hcoord_bound i) k
      (Nat.le_trans (Finset.le_sup' (f := fun j => Classical.choose (hcoord_bound j)) (mem_univ i)) hk)
  have hsum : dist (f k) l ^ 2 < (n : ℝ) * bound ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    have hlt : ∑ i : ι, dist ((f k) i) (l i) ^ 2 < ∑ i : ι, bound ^ 2 := by
      refine Finset.sum_lt_sum (fun i _ => ?_) ?_
      · have hdist_nonneg : 0 ≤ dist ((f k) i) (l i) :=
          @dist_nonneg ℝ _ ((f k).ofLp i) (l.ofLp i)
        nlinarith [hdist_nonneg, sq_nonneg bound, hcoord i]
      · cases ‹Nonempty ι› with | intro i0 =>
        have hdist_nonneg : 0 ≤ dist ((f k) i0) (l i0) :=
          @dist_nonneg ℝ _ ((f k).ofLp i0) (l.ofLp i0)
        refine ⟨i0, mem_univ i0, ?_⟩
        nlinarith [hdist_nonneg, sq_nonneg bound, hcoord i0]
    simpa [Finset.sum_const, nsmul_eq_mul] using hlt
  have hbound_eq : Real.sqrt ((n : ℝ) * bound ^ 2) = ε := by
    simp only [bound, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    field_simp [Nat.cast_pos.mpr hn]
    exact Real.sqrt_sq (le_of_lt hε)
  have hnonneg : 0 ≤ dist (f k) l := @dist_nonneg (EuclideanSpace ℝ ι) _ (f k) l
  calc
    dist (f k) l = Real.sqrt (dist (f k) l ^ 2) := (Real.sqrt_sq hnonneg).symm
    _ < Real.sqrt ((n : ℝ) * bound ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) hsum
    _ = ε := hbound_eq

private lemma cdExpectationStat_tendsto_modelExpectationStat_vector (order : List U) (h : IsFullSweep order)
    (T : Temperature) (p : Params ℝ U) (s₀ : State) :
    Tendsto (fun k => expectationStat (cdNegativePhaseMeasure k order p T s₀)) atTop
      (𝓝 (modelExpectationStat T p)) := by
  refine tendsto_euclidean_of_forall_coord fun i => ?_
  simpa [expectationStat, WithLp.ofLp_toLp] using
    cdExpectationStat_tendsto_modelExpectationStat order h T p s₀ i

/-- **Main result:** CD-k learning direction converges to `exactLearningDirection` (coordinate-wise). -/
theorem cdLearningDirection_tendsto_exactLearningDirection_coord (order : List U) (h : IsFullSweep order)
    (T : Temperature) (p : Params ℝ U) (s₀ : State) (i : I U) :
    Tendsto (fun k => (cdLearningDirection k order T p s₀) i) atTop
      (𝓝 (exactLearningDirection T p s₀ i)) := by
  have hneg := cdExpectationStat_tendsto_modelExpectationStat order h T p s₀ i
  have hpos := expectationStat_dirac s₀ i
  simp [cdLearningDirection, exactLearningDirection, learningRule, updateDir, expectationStat,
    WithLp.ofLp_toLp, hpos]
  exact hneg.const_sub (statCoord i s₀)

/-- **Main result:** CD-k learning direction converges to `exactLearningDirection` in `Θ U`. -/
theorem cdLearningDirection_tendsto_exactLearningDirection (order : List U) (h : IsFullSweep order)
    (T : Temperature) (p : Params ℝ U) (s₀ : State) :
    Tendsto (fun k => cdLearningDirection k order T p s₀) atTop
      (𝓝 (exactLearningDirection T p s₀)) := by
  have hneg := cdExpectationStat_tendsto_modelExpectationStat_vector order h T p s₀
  have hsub :=
    Filter.Tendsto.sub
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => expectationStat (positivePhaseAtData s₀)) atTop
          (𝓝 (expectationStat (positivePhaseAtData s₀))))
      hneg
  have hEq : ∀ k, cdLearningDirection k order T p s₀ =
      expectationStat (positivePhaseAtData s₀) -
        expectationStat (cdNegativePhaseMeasure k order p T s₀) := by
    intro k
    simp [cdLearningDirection, learningRule, updateDir, expectationStat_sub_eq_updateDir]
  simpa [hEq, exactLearningDirection, expectationStat_pos_dirac, modelExpectationStat] using hsub

/-- CD-k learning direction converges coordinate-wise to the learning direction. -/
theorem cdLearningDirection_tendsto_learningDirection_coord (order : List U) (h : IsFullSweep order)
    (T : Temperature) (p : Params ℝ U) (s₀ : State) (i : I U) :
    Tendsto (fun k => (cdLearningDirection k order T p s₀) i) atTop
      (𝓝 (learningDirection T p s₀ i)) := by
  rw [← exactLearningDirection_eq_learningDirection]
  exact cdLearningDirection_tendsto_exactLearningDirection_coord order h T p s₀ i

/-- CD-k learning direction converges in `Θ U` to the learning direction. -/
theorem cdLearningDirection_tendsto_learningDirection (order : List U) (h : IsFullSweep order)
    (T : Temperature) (p : Params ℝ U) (s₀ : State) :
    Tendsto (fun k => cdLearningDirection k order T p s₀) atTop
      (𝓝 (learningDirection T p s₀)) := by
  rw [← exactLearningDirection_eq_learningDirection]
  exact cdLearningDirection_tendsto_exactLearningDirection order h T p s₀

end ZeroOne

end BoltzmannLearningQuiver

end NeuralNetwork

#lint only docBlame docBlameThm
