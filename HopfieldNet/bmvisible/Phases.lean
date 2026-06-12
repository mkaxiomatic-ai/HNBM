/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.bmvisible.Bridge
import HopfieldNet.BoltzmannLearningQuiver.LearningRule

/-!
# Positive and negative BM learning phases (visible/hidden)

**Negative phase:** full-network Boltzmann measure (`negativePhaseMeasure`).

**Positive phase (learning):** visible pattern fixed; `k` hidden-only Gibbs sweeps (`positiveCdPMF`).

**Exact target:** data statistic at the clamped visible pattern minus model statistic at equilibrium.
-/

namespace BMVisible

open NeuralNetwork MeasureTheory ProbabilityTheory BoltzmannLearningQuiver ZeroOne BM
open scoped Temperature BigOperators

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable (part : VisibleHiddenPartition U)

/-- Positive phase measure after CD-$k$ on hidden units (visible pattern fixed). -/
noncomputable def positivePhaseMeasure (k : ℕ) (order : List U) (p : BMParams ℝ U part) (T : Temperature)
    (vp : VisiblePattern (R := ℝ) part) : Measure (BMState ℝ U part) :=
  (positiveCdPMF part k order p T vp).toMeasure

/-- Sufficient-statistic coordinate on visible/hidden states. -/
noncomputable def bmStatCoord (i : I U) (s : BMState ℝ U part) : ℝ :=
  statCoord i (toZeroOneState part s)

/-- Vector statistic expectation `E_μ[stat]`. -/
noncomputable def expectationStat (μ : Measure (BMState ℝ U part)) : Θ U :=
  WithLp.toLp 2 fun i => BM.expectation μ (bmStatCoord part i)

/-- Model statistic under Boltzmann equilibrium. -/
noncomputable def modelExpectationStat (T : Temperature) (p : BMParams ℝ U part) : Θ U :=
  expectationStat part (negativePhaseMeasure part p T)

/-- Clamped visible pattern as a full network state (hidden units at $0$). -/
noncomputable def dataState (vp : VisiblePattern (R := ℝ) part) : BMState ℝ U part :=
  visiblePatternToState part vp

/-- Exact BM learning direction at a visible pattern. -/
noncomputable def learningDirection (T : Temperature) (p : BMParams ℝ U part)
    (vp : VisiblePattern (R := ℝ) part) : Θ U :=
  bmStat part (dataState part vp) - modelExpectationStat part T p

/-- Positive phase at $k = 0$: Dirac at the clamped pattern state. -/
lemma positivePhaseMeasure_zero (order : List U) (p : BMParams ℝ U part) (T : Temperature)
    (vp : VisiblePattern (R := ℝ) part) :
    positivePhaseMeasure part 0 order p T vp = Measure.dirac (dataState part vp) := by
  simp [positivePhaseMeasure, positiveCdPMF, Nat.rec_zero, dataState, PMF.toMeasure_pure]

/-- Expectation under Dirac at clamped data state. -/
lemma expectationStat_dirac (vp : VisiblePattern (R := ℝ) part) (i : I U) :
    BM.expectation (Measure.dirac (dataState part vp)) (bmStatCoord part i) =
      bmStatCoord part i (dataState part vp) := by
  simp [BM.expectation, bmStatCoord]

/-- Vector expectation under Dirac at clamped data state. -/
lemma expectationStat_data (vp : VisiblePattern (R := ℝ) part) :
    expectationStat part (Measure.dirac (dataState part vp)) = bmStat part (dataState part vp) := by
  ext i
  simp [expectationStat, bmStat, bmStatCoord, expectationStat_dirac, statCoord, stat, WithLp.ofLp_toLp]

/-- Contrastive update from phase measures. -/
noncomputable def exactLearningDirection (T : Temperature) (p : BMParams ℝ U part)
    (vp : VisiblePattern (R := ℝ) part) : Θ U :=
  expectationStat part (Measure.dirac (dataState part vp)) -
    expectationStat part (negativePhaseMeasure part p T)

/-- At clamped data, exact direction equals `learningDirection`. -/
theorem exactLearningDirection_eq_learningDirection (T : Temperature) (p : BMParams ℝ U part)
    (vp : VisiblePattern (R := ℝ) part) :
    exactLearningDirection part T p vp = learningDirection part T p vp := by
  simp [exactLearningDirection, learningDirection, modelExpectationStat, expectationStat_data]

/-- Contrastive update from arbitrary phase measures. -/
noncomputable def updateDir (pos neg : Measure (BMState ℝ U part)) : Θ U :=
  expectationStat part pos - expectationStat part neg

/-- Vector statistic difference equals `updateDir`. -/
lemma expectationStat_sub_eq_updateDir (pos neg : Measure (BMState ℝ U part)) :
    expectationStat part pos - expectationStat part neg = updateDir part pos neg := by
  ext i
  simp [expectationStat, updateDir, WithLp.ofLp_sub, WithLp.ofLp_toLp]

/-- Verified `BM.LearningRule` on visible/hidden states. -/
noncomputable def learningRule : LearningRule (Θ U) (BMState ℝ U part) where
  updateDir := updateDir part
  I := I U
  stat := fun i => bmStatCoord part i
  coord := coord
  correct := by intro _ _ _; rfl

/-- Exact learning direction from clamped data vs equilibrium negative phase. -/
noncomputable def updateDirData (T : Temperature) (p : BMParams ℝ U part)
    (vp : VisiblePattern (R := ℝ) part) : Θ U :=
  learningRule part |>.updateDir (Measure.dirac (dataState part vp)) (negativePhaseMeasure part p T)

/-- `updateDirData` equals `exactLearningDirection`. -/
theorem updateDirData_eq_exactLearningDirection (T : Temperature) (p : BMParams ℝ U part)
    (vp : VisiblePattern (R := ℝ) part) :
    updateDirData part T p vp = exactLearningDirection part T p vp := by
  ext i
  simp [updateDirData, learningRule, updateDir, exactLearningDirection, expectationStat,
    WithLp.ofLp_sub, WithLp.ofLp_toLp]

/-- `updateDirData` equals `learningDirection`. -/
theorem updateDirData_eq_learningDirection (T : Temperature) (p : BMParams ℝ U part)
    (vp : VisiblePattern (R := ℝ) part) :
    updateDirData part T p vp = learningDirection part T p vp := by
  rw [updateDirData_eq_exactLearningDirection, exactLearningDirection_eq_learningDirection]

end BMVisible

#lint only docBlame
