/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.Phases

/-!
# Verified `BM.LearningRule` on quiver states

Contrastive update `E_pos[stat] - E_neg[stat]` as a `BM.LearningRule`.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace ZeroOne

open MeasureTheory BoltzmannLearningQuiver.BM

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Contrastive update direction from phase measures. -/
noncomputable def updateDir (pos neg : Measure (State ℝ U)) : Θ U :=
  WithLp.toLp 2 fun i =>
    BM.expectation pos (statCoord i) - BM.expectation neg (statCoord i)

/-- Verified `BM.LearningRule` for quiver symmetric-binary statistics. -/
noncomputable def learningRule : BM.LearningRule (Θ U) (State ℝ U) where
  updateDir := updateDir
  I := I U
  stat := statCoord
  coord := coord
  correct := by intro _ _ _; rfl

/-- Exact learning direction for one data state at `(p, T)`. -/
noncomputable def updateDirData (T : Temperature) (p : Params ℝ U) (s_data : State ℝ U) : Θ U :=
  learningRule.updateDir (positivePhaseAtData s_data) (negativePhaseMeasure T p)

/-- Vector statistic difference equals `updateDir`. -/
lemma expectationStat_sub_eq_updateDir (pos neg : Measure (State ℝ U)) :
    expectationStat pos - expectationStat neg = updateDir pos neg := by
  ext i
  simp [expectationStat, updateDir, WithLp.ofLp_sub, WithLp.ofLp_toLp]

/-- `updateDirData` equals `exactLearningDirection`. -/
theorem updateDirData_eq_exactLearningDirection (T : Temperature) (p : Params ℝ U) (s_data : State ℝ U) :
    updateDirData T p s_data = exactLearningDirection T p s_data := by
  ext i
  simp [updateDirData, learningRule, updateDir, exactLearningDirection, expectationStat,
    WithLp.ofLp_sub, WithLp.ofLp_toLp]

/-- `updateDirData` equals `learningDirection`. -/
theorem updateDirData_eq_learningDirection (T : Temperature) (p : Params ℝ U) (s_data : State ℝ U) :
    updateDirData T p s_data = learningDirection T p s_data := by
  rw [updateDirData_eq_exactLearningDirection, exactLearningDirection_eq_learningDirection]

end ZeroOne
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
