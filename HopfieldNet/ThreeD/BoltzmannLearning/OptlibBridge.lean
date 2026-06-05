import HopfieldNet.ThreeD.BoltzmannLearning.Core
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
## Bridge: BM learning directions → optimization (Optlib-compatible hook)

Optlib’s gradient-descent results are stated under analytic hypotheses (`HasGradientAt`,
Lipschitz gradient, convexity, …). For BM learning these hypotheses are *not* automatic:

- the objective is typically a KL divergence / log-likelihood,
- gradients require exchanging differentiation and summation/integration,
- and in the infinite-lattice setting one uses DLR specifications and limits.

So this file is intentionally minimal and does **not** import Optlib directly (Optlib may not be
buildable in every project configuration). It provides a small hook that matches Optlib’s
expectations: “objective + certified gradient”, plus a single GD step map.
-/

namespace NeuralNetwork

namespace ThreeD

namespace BoltzmannLearning

namespace OptlibBridge

open scoped InnerProductSpace Gradient

/-- Package “objective + gradient” in the form expected by Optlib. -/
structure Objective (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] where
  L : Θ → ℝ
  grad : Θ → Θ
  hasGrad : ∀ θ, HasGradientAt L (grad θ) θ

/-|
Once you have `Objective` plus step-size and smoothness hypotheses, you can instantiate the
corresponding Optlib gradient-descent structures and reuse convergence theorems.

We do **not** assert smoothness/convexity here: those are the nontrivial BM theorems.
-/
noncomputable def gradientDescentFixStep
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (obj : Objective Θ) (_θ0 : Θ) (a : ℝ) :
    Θ → Θ :=
  fun θ => θ - a • obj.grad θ

end OptlibBridge

end BoltzmannLearning

end ThreeD

end NeuralNetwork
