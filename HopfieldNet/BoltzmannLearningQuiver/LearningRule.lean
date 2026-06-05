/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.Phases
import HopfieldNet.ThreeD.BoltzmannLearning.Core

/-!
## Learning-rule interface on Quiver state measures

Packages the coordinate-wise update `E_pos[φ] - E_neg[φ]` using vector expectations on
`Θ`. Measure-theoretic phases on `Measure (State ℝ U)` can be added once clamp kernels
are wired in.
-/

namespace NeuralNetwork

namespace BoltzmannLearningQuiver

namespace SymmetricBinary

open ThreeD.BoltzmannLearning VectorGibbs

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Coordinate statistic `φ_i(s) = stat(s) i`. -/
noncomputable def statCoord (i : I U) (s : State ℝ U) : ℝ :=
  (WithLp.ofLp (stat s)) i

/-- Read coordinate `i` from a parameter vector. -/
def coord (θ : Θ U) (i : I U) : ℝ :=
  (WithLp.ofLp θ) i

/-- Update direction from coordinate-wise expectation differences. -/
noncomputable def updateDir (posStat negStat : Θ U) : Θ U :=
  posStat - negStat

/-- Learning direction for one data state against the model expectation at `(p,T)`. -/
noncomputable def updateDirData (T : Temperature) (p : Params ℝ U) (s_data : State ℝ U) : Θ U :=
  updateDir (stat s_data) (modelExpectationStat T p)

theorem updateDirData_eq_learningDirection (T : Temperature) (p : Params ℝ U) (s_data : State ℝ U) :
    updateDirData T p s_data = learningDirection T p s_data := by
  rfl

theorem updateDirData_eq_negLogLik_gradient (T : Temperature) (p : Params ℝ U) (s_data : State ℝ U) :
    updateDirData T p s_data =
      stat s_data - expectation (X := State ℝ U) (Θ := Θ U) stat (thetaFromParams p) := by
  rw [updateDirData_eq_learningDirection, learningDirection_eq_negLogLik_gradient]

end SymmetricBinary

end BoltzmannLearningQuiver

end NeuralNetwork
