/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.bmvisible.SequentialSweepUnique
import HopfieldNet.bmvisible.ContrastiveDivergence
import MCMC.toKernel
import MCMC.DetailedBalanceGen

/-!
# Equivalence of sequential Gibbs dynamics layers
-/

namespace BMVisible

open Classical MeasureTheory ProbabilityTheory TwoState HopfieldBoltzmann Matrix
open scoped ProbabilityTheory ENNReal BigOperators

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable {part : VisibleHiddenPartition U}

local notation "State" => BMState ℝ U part

private lemma measure_eq_sum_singletons {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (m : Measure α) (S : Set α) :
    m S = Finset.sum (Finset.univ.filter (fun s => s ∈ S)) (fun s => m {s}) := by
  let F : Finset α := Finset.univ.filter (fun s => s ∈ S)
  have hU : (⋃ s ∈ F, ({s} : Set α)) = S := by ext x; simp [F]
  have hdisj :
      Set.PairwiseDisjoint (↑F : Set α) (fun s : α => ({s} : Set α)) := by
    intro a ha b hb hab
    exact Set.disjoint_singleton.2 hab
  simpa [F, hU] using
    (measure_biUnion_finset (μ := m) (s := F) (f := fun s : α => ({s} : Set α)) hdisj (_))

private lemma gibbsUpdate_prob_eq_SSrow (u : U) (p : BMParams ℝ U part) (T : Temperature)
    (s t : State) :
    (TwoState.gibbsUpdate (NN := NN ℝ U part) (RingHom.id ℝ) p T s u) t =
      ENNReal.ofReal (SSrow u p T s t) := by
  have hkernel :
      (singleSiteKernel (NN := NN ℝ U part) (energySpec part) p T u) s {t} =
        (TwoState.gibbsUpdate (NN := NN ℝ U part) (RingHom.id ℝ) p T s u) t := by
    unfold singleSiteKernel pmfToKernel
    simp_rw [Kernel.ofFunOfCountable_apply, PMF.toMeasure_singleton]
  have hfin :
      (TwoState.gibbsUpdate (NN := NN ℝ U part) (RingHom.id ℝ) p T s u) t ≠ ⊤ :=
    (PMF.apply_lt_top (TwoState.gibbsUpdate (NN := NN ℝ U part) (RingHom.id ℝ) p T s u) t).ne
  dsimp [SSrow]
  rw [← hkernel]
  simp [ENNReal.ofReal_toReal, hfin]

/-- One sequential Gibbs sweep: PMF probability equals `sweepRowMatrix` entry. -/
theorem gibbsSweep_prob_eq_sweepRowMatrix (order : List U) (p : BMParams ℝ U part) (T : Temperature)
    (s t : State) :
    (TwoState.gibbsSweep (NN := NN ℝ U part) order p T (RingHom.id ℝ) s) t =
      ENNReal.ofReal (sweepRowMatrix p T order s t) := by
  induction order generalizing s t with
  | nil =>
      simp only [TwoState.gibbsSweep, TwoState.gibbsSweep_nil, TwoState.gibbsSweepAux_nil,
        sweepRowMatrix, Matrix.one_apply, PMF.pure_apply]
      by_cases ht : t = s
      · subst ht; simp [ENNReal.ofReal_one]
      · simp [Ne.symm ht, ENNReal.ofReal_zero]
        exact ht
  | cons u us ih =>
      calc
        (TwoState.gibbsSweep (NN := NN ℝ U part) (u :: us) p T (RingHom.id ℝ) s) t
            = ∑' sMid, (TwoState.gibbsUpdate (NN := NN ℝ U part) (RingHom.id ℝ) p T s u) sMid *
                (TwoState.gibbsSweep (NN := NN ℝ U part) us p T (RingHom.id ℝ) sMid) t := by
              rw [TwoState.gibbsSweep_cons]
              change (PMF.bind (TwoState.gibbsUpdate (NN := NN ℝ U part) (RingHom.id ℝ) p T s u)
                  (fun sMid => TwoState.gibbsSweep (NN := NN ℝ U part) us p T (RingHom.id ℝ) sMid)) t = _
              rw [PMF.bind_apply, tsum_fintype]
        _ = ∑' sMid, ENNReal.ofReal (SSrow u p T s sMid) *
              ENNReal.ofReal (sweepRowMatrix p T us sMid t) := by
              congr with sMid
              rw [gibbsUpdate_prob_eq_SSrow, ih]
        _ = ENNReal.ofReal (∑ sMid, SSrow u p T s sMid * sweepRowMatrix p T us sMid t) := by
              rw [tsum_fintype]
              have hnn : ∀ sMid ∈ (Finset.univ : Finset State),
                  0 ≤ SSrow u p T s sMid * sweepRowMatrix p T us sMid t := by
                intro sMid _
                exact mul_nonneg (SSrow_nonneg u p T s sMid) (sweepRowMatrix_nonneg us p T sMid t)
              refine (Finset.sum_congr rfl fun sMid _ => ?_).trans (ENNReal.ofReal_sum_of_nonneg hnn).symm
              simp [ENNReal.ofReal_mul, SSrow_nonneg, sweepRowMatrix_nonneg]
        _ = ENNReal.ofReal (sweepRowMatrix p T (u :: us) s t) := by
              simp [sweepRowMatrix, Matrix.mul_apply]

private lemma matrixToKernel_singleton_eval (P : Matrix State State ℝ) (hP : IsStochastic P)
    (s t : State) :
    (matrixToKernel P hP) s {t} = ENNReal.ofReal (P s t) := by
  change ((∑ x : State, ENNReal.ofReal (P s x) • Measure.dirac x) : Measure State) {t}
      = ENNReal.ofReal (P s t)
  simp [Measure.dirac_apply']
  rw [Finset.sum_eq_single t]
  · simp
  · intro x _ hx; simp [hx]
  · simp

private lemma kernel_eq_of_singleton_eval {κ η : Kernel State State}
    (h : ∀ s t, κ s {t} = η s {t}) : κ = η := by
  ext s B hB
  let F := Finset.univ.filter (fun t => t ∈ B)
  have hsum₁ : κ s B = Finset.sum F (fun t => κ s {t}) := by
    simpa [F] using measure_eq_sum_singletons (m := κ s) B
  have hsum₂ : η s B = Finset.sum F (fun t => η s {t}) := by
    simpa [F] using measure_eq_sum_singletons (m := η s) B
  rw [hsum₁, hsum₂]
  refine Finset.sum_congr rfl fun t _ => h s t

/-- Single-site row matrix induces the same kernel as `singleSiteKernel`. -/
theorem matrixToKernel_SSrow_eq_singleSiteKernel (u : U) (p : BMParams ℝ U part) (T : Temperature) :
    matrixToKernel (SSrow u p T) (SSrow_isStochastic u p T) =
      singleSiteKernel (NN := NN ℝ U part) (energySpec part) p T u :=
  kernel_eq_of_singleton_eval fun s t => by
    rw [matrixToKernel_singleton_eval, singleSiteKernel_singleton_eval]
    exact congrArg ENNReal.ofReal (SSrow_eq_Kbm u p T s t)

private lemma matrixToKernel_sweepRowMatrix_eq_sequentialSweepKernel_aux (order : List U)
    (p : BMParams ℝ U part) (T : Temperature) :
    matrixToKernel (sweepRowMatrix p T order) (sweepRowMatrix_isStochastic order p T) =
      sequentialSweepKernel part p T order := by
  induction order with
  | nil =>
      apply kernel_eq_of_singleton_eval
      intro s t
      by_cases ht : s = t
      · subst ht; simp [matrixToKernel_singleton_eval, sequentialSweepKernel, sweepRowMatrix,
          Matrix.one_apply, Kernel.id_apply, ENNReal.ofReal_one]
      · simp [matrixToKernel_singleton_eval, sequentialSweepKernel, sweepRowMatrix,
          Matrix.one_apply, Kernel.id_apply, ht, ENNReal.ofReal_zero]
  | cons u us ih =>
      have hcomp :
          matrixToKernel (sweepRowMatrix p T (u :: us))
              (sweepRowMatrix_isStochastic (u :: us) p T) =
            (matrixToKernel (sweepRowMatrix p T us) (sweepRowMatrix_isStochastic us p T)) ∘ₖ
              (matrixToKernel (SSrow u p T) (SSrow_isStochastic u p T)) := by
        apply kernel_eq_of_singleton_eval
        intro s t
        dsimp [sweepRowMatrix]
        rw [matrixToKernel_singleton_eval (SSrow u p T * sweepRowMatrix p T us)
            (isStochastic_mul (SSrow_isStochastic u p T) (sweepRowMatrix_isStochastic us p T)),
          matrixToKernel_comp_singleton (P := SSrow u p T) (Q := sweepRowMatrix p T us)
            (hP := SSrow_isStochastic u p T) (hQ := sweepRowMatrix_isStochastic us p T)]
      rw [hcomp, ih, matrixToKernel_SSrow_eq_singleSiteKernel, sequentialSweepKernel_cons]

/-- **Main equivalence:** full sweep row matrix kernel = `sequentialSweepKernel`. -/
theorem matrixToKernel_sweepRowMatrix_eq_sequentialSweepKernel (order : List U)
    (p : BMParams ℝ U part) (T : Temperature) :
    matrixToKernel (sweepRowMatrix p T order) (sweepRowMatrix_isStochastic order p T) =
      sequentialSweepKernel part p T order :=
  matrixToKernel_sweepRowMatrix_eq_sequentialSweepKernel_aux order p T

/-- Sequential sweep kernel singleton mass equals `sweepRowMatrix` entry. -/
theorem sequentialSweepKernel_eval_singleton (order : List U) (p : BMParams ℝ U part) (T : Temperature)
    (s t : State) :
    (sequentialSweepKernel part p T order) s {t} =
      ENNReal.ofReal (sweepRowMatrix p T order s t) := by
  rw [← matrixToKernel_sweepRowMatrix_eq_sequentialSweepKernel order p T,
    matrixToKernel_singleton_eval (sweepRowMatrix p T order)
      (sweepRowMatrix_isStochastic order p T) s t]

/-- PMF measure singleton mass equals sequential sweep kernel singleton mass. -/
theorem gibbsSweep_toMeasure_singleton_eq_kernel (order : List U) (p : BMParams ℝ U part) (T : Temperature)
    (s t : State) :
    (TwoState.gibbsSweep (NN := NN ℝ U part) order p T (RingHom.id ℝ) s).toMeasure {t} =
      (sequentialSweepKernel part p T order) s {t} := by
  rw [PMF.toMeasure_singleton, gibbsSweep_prob_eq_sweepRowMatrix order p T s t,
    sequentialSweepKernel_eval_singleton order p T s t]

/-- Kernel obtained by lifting one-sweep Gibbs PMFs to a Markov kernel. -/
noncomputable def gibbsSweepKernel (order : List U) (p : BMParams ℝ U part) (T : Temperature) :
    Kernel State State :=
  pmfToKernel fun s =>
    TwoState.gibbsSweep (NN := NN ℝ U part) order p T (RingHom.id ℝ) s

/-- PMF-lifted sweep kernel equals `sequentialSweepKernel`. -/
theorem gibbsSweepKernel_eq_sequentialSweepKernel (order : List U) (p : BMParams ℝ U part)
    (T : Temperature) :
    gibbsSweepKernel order p T = sequentialSweepKernel part p T order :=
  kernel_eq_of_singleton_eval fun s t => by
    dsimp [gibbsSweepKernel, pmfToKernel]
    simp only [Kernel.ofFunOfCountable_apply, PMF.toMeasure_singleton]
    exact (gibbsSweep_prob_eq_sweepRowMatrix order p T s t).trans
      (sequentialSweepKernel_eval_singleton order p T s t).symm

/-- One CD step on PMFs equals matrix multiplication by `sweepRowMatrix`. -/
theorem cdStepPMF_apply_eq_sweepRowMatrix (order : List U) (p : BMParams ℝ U part) (T : Temperature)
    (μ : PMF State) (t : State) :
    (cdStepPMF part order p T μ) t =
      ∑ s : State, μ s * ENNReal.ofReal (sweepRowMatrix p T order s t) := by
  simp [cdStepPMF, PMF.bind_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [gibbsSweep_prob_eq_sweepRowMatrix order p T s t]

/-- Dirac probability vector at state `s₀` on the finite state simplex. -/
noncomputable def diracSimplex (s₀ : State) : stdSimplex ℝ State :=
{ val := fun s => if s = s₀ then 1 else 0
  property := by
    refine ⟨?_, ?_⟩
    · intro s; by_cases h : s = s₀ <;> simp [h]
    · classical
      simp [Finset.sum_ite_eq', Finset.mem_univ] }

/-- Dirac simplex vector assigns mass one at its base state. -/
lemma diracSimplex_apply_self (s₀ : State) : (diracSimplex s₀).val s₀ = 1 := by
  simp [diracSimplex]

/-- Dirac simplex vector assigns mass zero off the base state. -/
lemma diracSimplex_apply_ne {s₀ s : State} (h : s ≠ s₀) : (diracSimplex s₀).val s = 0 := by
  simp [diracSimplex, h]

/-- Dirac simplex entries are nonnegative. -/
lemma diracSimplex_nonneg (s₀ s : State) : 0 ≤ (diracSimplex s₀).val s := by
  simp [diracSimplex]
  split_ifs <;> norm_num

private lemma distributionAtTime_succ (P : Matrix State State ℝ) (μ₀ : stdSimplex ℝ State) (k : ℕ)
    (t : State) :
    distributionAtTime P μ₀ (k + 1) t =
      ∑ s, distributionAtTime P μ₀ k s * P s t := by
  simp only [distributionAtTime]
  calc
    ((P ^ (k + 1))ᵀ *ᵥ μ₀.val) t
        = ((Pᵀ * (Pᵀ ^ k)) *ᵥ μ₀.val) t := by
          simp [pow_succ, Matrix.transpose_mul, Matrix.transpose_pow]
    _ = (Pᵀ *ᵥ ((Pᵀ ^ k) *ᵥ μ₀.val)) t := by simp only [Matrix.mulVec_mulVec]
    _ = ∑ s, P s t * ((Pᵀ ^ k) *ᵥ μ₀.val) s := by
          simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    _ = ∑ s, distributionAtTime P μ₀ k s * P s t := by simp [distributionAtTime, mul_comm]

/-- CD-$k$ distribution entries from a Dirac start are nonnegative. -/
lemma distributionAtTime_dirac_nonneg (order : List U) (p : BMParams ℝ U part) (T : Temperature)
    (s₀ : State) :
    ∀ k s, 0 ≤ distributionAtTime (sweepRowMatrix p T order) (diracSimplex s₀) k s := by
  intro k s
  induction k generalizing s with
  | zero =>
      simp [distributionAtTime, diracSimplex]
      split_ifs <;> norm_num
  | succ k ih =>
      rw [distributionAtTime_succ (sweepRowMatrix p T order) (diracSimplex s₀) k s]
      apply Finset.sum_nonneg
      intro sMid _
      exact mul_nonneg (ih sMid) (sweepRowMatrix_nonneg order p T sMid s)

/-- **CD-k bridge:** CD-k PMF equals `distributionAtTime` from Dirac at `s₀`. -/
theorem cdNegativePMF_apply_eq_distributionAtTime (k : ℕ) (order : List U) (p : BMParams ℝ U part)
    (T : Temperature) (s₀ t : State) :
    (cdNegativePMF part k order p T s₀) t =
      ENNReal.ofReal (distributionAtTime (sweepRowMatrix p T order) (diracSimplex s₀) k t) := by
  induction k generalizing s₀ t with
  | zero =>
      have hdist :
          distributionAtTime (sweepRowMatrix p T order) (diracSimplex s₀) 0 t = if t = s₀ then 1 else 0 := by
        by_cases ht : t = s₀
        · subst ht
          simp [distributionAtTime, diracSimplex, Matrix.mulVec, Matrix.one_apply, Matrix.transpose_apply,
            dotProduct, Finset.sum_ite_eq', Finset.mem_univ]
        · have hne : t ≠ s₀ := fun h => ht h
          calc distributionAtTime (sweepRowMatrix p T order) (diracSimplex s₀) 0 t
              = (∑ j, (if j = t then 1 else 0) * (diracSimplex s₀).val j) := by
                  simp [distributionAtTime, Matrix.mulVec, Matrix.one_apply, Matrix.transpose_apply,
                    dotProduct]
            _ = (diracSimplex s₀).val t := by simp [Finset.sum_ite_eq', Finset.mem_univ]
            _ = 0 := diracSimplex_apply_ne hne
            _ = if t = s₀ then 1 else 0 := by simp [hne]
      simp only [cdNegativePMF, Nat.rec_zero, PMF.pure_apply, hdist]
      split_ifs <;> simp [ENNReal.ofReal_one, ENNReal.ofReal_zero]
  | succ k ih =>
      have hstep :=
        cdStepPMF_apply_eq_sweepRowMatrix order p T (cdNegativePMF part k order p T s₀) t
      have hdist := distributionAtTime_succ (sweepRowMatrix p T order) (diracSimplex s₀) k t
      calc
        (cdNegativePMF part (k + 1) order p T s₀) t
            = ∑ s, (cdNegativePMF part k order p T s₀) s *
                ENNReal.ofReal (sweepRowMatrix p T order s t) := hstep
        _ = ∑ s, ENNReal.ofReal
                (distributionAtTime (sweepRowMatrix p T order) (diracSimplex s₀) k s) *
              ENNReal.ofReal (sweepRowMatrix p T order s t) := by
              refine Finset.sum_congr rfl fun s _ => ?_
              rw [ih s₀ s]
        _ = ENNReal.ofReal
              (∑ s, distributionAtTime (sweepRowMatrix p T order) (diracSimplex s₀) k s *
                sweepRowMatrix p T order s t) := by
              have hnn : ∀ s ∈ (Finset.univ : Finset State),
                  0 ≤ distributionAtTime (sweepRowMatrix p T order) (diracSimplex s₀) k s *
                    sweepRowMatrix p T order s t := by
                intro s _
                exact mul_nonneg (distributionAtTime_dirac_nonneg order p T s₀ k s)
                  (sweepRowMatrix_nonneg order p T s t)
              refine (Finset.sum_congr rfl fun s _ => ?_).trans (ENNReal.ofReal_sum_of_nonneg hnn).symm
              simp [ENNReal.ofReal_mul, distributionAtTime_dirac_nonneg, sweepRowMatrix_nonneg]
        _ = ENNReal.ofReal
              (distributionAtTime (sweepRowMatrix p T order) (diracSimplex s₀) (k + 1) t) := by
              simp [hdist]

end BMVisible

#lint only docBlame
