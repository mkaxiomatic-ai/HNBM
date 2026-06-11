/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.Core
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Optlib-compatible optimization hook

Objective + certified gradient; no Optlib import.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace OptlibBridge

open scoped InnerProductSpace Gradient

/-- Objective function with a certified gradient. -/
structure Objective (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] where
  /-- Loss function `L(θ)`. -/
  L : Θ → ℝ
  /-- Certified gradient field. -/
  grad : Θ → Θ
  /-- Gradient certification at every point. -/
  hasGrad : ∀ θ, HasGradientAt L (grad θ) θ

/-- One fixed-step gradient descent update. -/
noncomputable def gradientDescentFixStep
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (obj : Objective Θ) (_θ0 : Θ) (a : ℝ) : Θ → Θ :=
  fun θ => θ - a • obj.grad θ

end OptlibBridge
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
