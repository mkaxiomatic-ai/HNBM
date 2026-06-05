/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.Energy
import HopfieldNet.ThreeD.BoltzmannLearning.VectorGibbsLearning

/-!
## Exact Boltzmann learning gradient on Quiver `SymmetricBinary` states

Specializes the general `VectorGibbsLearning.hasGradientAt_negLogLik` theorem to
states and parameters from the Quiver library.
-/

namespace NeuralNetwork

namespace BoltzmannLearningQuiver

namespace SymmetricBinary

open ThreeD.BoltzmannLearning VectorGibbs

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Single-sample negative log-likelihood for a Quiver state `s₀`. -/
noncomputable abbrev negLogLik (s₀ : State ℝ U) (θ : Θ U) : ℝ :=
  VectorGibbs.negLogLik (X := State ℝ U) (Θ := Θ U) stat s₀ θ

/-- **Standard BM learning rule (exact):** data statistic minus model statistic. -/
theorem hasGradientAt_negLogLik (s₀ : State ℝ U) (θ : Θ U) :
    HasGradientAt (fun θ' : Θ U => negLogLik s₀ θ')
      (stat s₀ - expectation (X := State ℝ U) (Θ := Θ U) stat θ) θ := by
  simpa [negLogLik] using
    VectorGibbs.hasGradientAt_negLogLik (X := State ℝ U) (Θ := Θ U) (stat := stat) s₀ θ

/-- At parameters induced from Quiver `Params`, the gradient uses `thetaFromParams p`. -/
theorem hasGradientAt_negLogLik_params (s₀ : State ℝ U) (p : Params ℝ U) :
    HasGradientAt (fun θ' : Θ U => negLogLik s₀ θ')
      (stat s₀ - expectation (X := State ℝ U) (Θ := Θ U) stat (thetaFromParams p))
      (thetaFromParams p) := by
  exact hasGradientAt_negLogLik s₀ (thetaFromParams p)

end SymmetricBinary

end BoltzmannLearningQuiver

end NeuralNetwork
