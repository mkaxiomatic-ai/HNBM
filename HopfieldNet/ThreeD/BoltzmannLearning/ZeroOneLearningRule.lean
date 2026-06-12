import HopfieldNet.ThreeD.BoltzmannLearning.Core
import HopfieldNet.ThreeD.BoltzmannLearning.ZeroOneInstantiation

/-!
## `LearningRule` instance for `{0,1}` Boltzmann features

Packages `ZeroOneInstantiation.stat` into the abstract BM learning-rule schema from
`BoltzmannLearning.Core`: each coordinate updates by `E_pos[φ_i] - E_neg[φ_i]`.

The gradient identity is in `ZeroOneLearning.lean` / `VectorGibbsLearning`.
-/

namespace NeuralNetwork
namespace ThreeD
namespace BoltzmannLearning

namespace ZeroOneInstantiation

noncomputable section

open MeasureTheory

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

abbrev I (U : Type) := U × U ⊕ U

/-- Coordinate statistic `φ_i` induced by `stat`. -/
def statCoord (i : I U) : BM.Stat U :=
  fun c => (WithLp.ofLp (stat (U := U) c)) i

/-- Read a parameter coordinate. -/
def coord (θ : Θ U) (i : I U) : ℝ :=
  (WithLp.ofLp θ) i

/-- Contrastive update direction from positive and negative phase measures. -/
def updateDir (pos neg : Measure (Config U)) : Θ U :=
  WithLp.toLp 2 (V := (I U → ℝ)) fun i =>
    BM.expectation pos (statCoord (U := U) i) - BM.expectation neg (statCoord (U := U) i)

/-- Canonical `{0,1}` BM learning rule. -/
def learningRule : BM.LearningRule (Θ U) U where
  updateDir := updateDir (U := U)
  I := I U
  stat := statCoord (U := U)
  coord := coord (U := U)
  correct := by
    intro pos neg i
    rfl

end

end ZeroOneInstantiation

end BoltzmannLearning
end ThreeD
end NeuralNetwork
