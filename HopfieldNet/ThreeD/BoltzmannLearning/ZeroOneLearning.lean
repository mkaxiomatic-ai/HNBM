import HopfieldNet.ThreeD.BoltzmannLearning.ZeroOneInstantiation
import HopfieldNet.ThreeD.BoltzmannLearning.VectorGibbsLearning

/-!
## Learning theorem for `{0,1}` Boltzmann features

Specializes the general exp-family gradient theorem to `ZeroOneInstantiation.stat`:

`∇θ (⟪stat(data), θ⟫ + log Z(θ)) = stat(data) - Eθ[stat]`.
-/

namespace NeuralNetwork
namespace ThreeD
namespace BoltzmannLearning

namespace ZeroOneInstantiation

noncomputable section

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

open VectorGibbs

/-- Single-sample neg log-likelihood gradient for `{0,1}` BM statistics. -/
theorem hasGradientAt_negLogLik
    (c0 : Config U) (θ : Θ U) :
    HasGradientAt
        (fun θ' : Θ U => VectorGibbs.negLogLik (X := Config U) (Θ := Θ U) (stat := stat (U := U)) c0 θ')
        (stat (U := U) c0 - expectation (X := Config U) (Θ := Θ U) (stat := stat (U := U)) θ) θ := by
  simpa using
    (VectorGibbs.hasGradientAt_negLogLik (X := Config U) (Θ := Θ U) (stat := stat (U := U)) c0 θ)

end

end ZeroOneInstantiation

end BoltzmannLearning
end ThreeD
end NeuralNetwork
