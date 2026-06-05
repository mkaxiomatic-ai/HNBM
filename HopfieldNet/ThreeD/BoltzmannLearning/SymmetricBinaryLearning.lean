import HopfieldNet.ThreeD.BoltzmannLearning.SymmetricBinaryInstantiation
import HopfieldNet.ThreeD.BoltzmannLearning.VectorGibbsLearning

/-!
## Learning theorem specialized to SymmetricBinary Hopfield features

This file just *specializes* the general exp-family gradient theorem to the concrete feature map
`SymmetricBinaryInstantiation.stat`.

It's the formal statement of “positive phase − negative phase” for Hopfield/BM parameters in the
finite case:

`∇θ (⟪stat(data), θ⟫ + log Z(θ)) = stat(data) - Eθ[stat]`.
-/

namespace NeuralNetwork
namespace ThreeD
namespace BoltzmannLearning

namespace SymmetricBinaryInstantiation

noncomputable section

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

open VectorGibbs

/-- Single-sample neg log-likelihood gradient for the Hopfield feature map. -/
theorem hasGradientAt_negLogLik
    (c0 : Config U) (θ : Θ U) :
    HasGradientAt
        (fun θ' : Θ U => VectorGibbs.negLogLik (X := Config U) (Θ := Θ U) (stat := stat (U := U)) c0 θ')
        (stat (U := U) c0 - expectation (X := Config U) (Θ := Θ U) (stat := stat (U := U)) θ) θ := by
  simpa using
    (VectorGibbs.hasGradientAt_negLogLik (X := Config U) (Θ := Θ U) (stat := stat (U := U)) c0 θ)

end

end SymmetricBinaryInstantiation

end BoltzmannLearning
end ThreeD
end NeuralNetwork
