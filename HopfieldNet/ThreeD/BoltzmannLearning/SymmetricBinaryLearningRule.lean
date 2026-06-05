import HopfieldNet.ThreeD.BoltzmannLearning.Core
import HopfieldNet.ThreeD.BoltzmannLearning.SymmetricBinaryInstantiation

/-!
## A `LearningRule` instance for SymmetricBinary Hopfield/BM features

This packages the concrete Hopfield feature map (`SymmetricBinaryInstantiation.stat`) into the
abstract BM learning-rule schema from `BoltzmannLearning.Core`:

each parameter coordinate is updated by the difference of expectations
`E_pos[φ_i] - E_neg[φ_i]`.

This is intentionally “theorem-light”: it is an interface adapter. The *theorem* that this update
matches a gradient of a likelihood objective is provided separately by the `VectorGibbsLearning`
layer and its SymmetricBinary specialization.
-/

namespace NeuralNetwork
namespace ThreeD
namespace BoltzmannLearning

namespace SymmetricBinaryInstantiation

noncomputable section

open MeasureTheory

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

abbrev I (U : Type) := U × U ⊕ U

/-- Coordinate statistic `φ_i` induced by the vector-valued feature map `stat`. -/
def statCoord (i : I U) : BM.Stat U :=
  fun c => (WithLp.ofLp (stat (U := U) c)) i

/-- Read a parameter coordinate. -/
def coord (θ : Θ U) (i : I U) : ℝ :=
  (WithLp.ofLp θ) i

/-- Update direction: vector whose coordinates are expectation differences. -/
def updateDir (pos neg : Measure (Config U)) : Θ U :=
  WithLp.toLp 2 (V := (I U → ℝ)) fun i =>
    BM.expectation pos (statCoord (U := U) i) - BM.expectation neg (statCoord (U := U) i)

/-- The canonical BM learning rule for SymmetricBinary Hopfield features. -/
def learningRule : BM.LearningRule (Θ U) U where
  updateDir := updateDir (U := U)
  I := I U
  stat := statCoord (U := U)
  coord := coord (U := U)
  correct := by
    intro pos neg i
    rfl

end

end SymmetricBinaryInstantiation

end BoltzmannLearning
end ThreeD
end NeuralNetwork
