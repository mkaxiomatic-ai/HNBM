/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.Quiver.NeuralNetwork.Main
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Quiver-native Boltzmann learning core

Abstract measure-theoretic schema for BM learning on configuration type `X`.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver

open ProbabilityTheory MeasureTheory

/-- Energy-based Boltzmann model on configuration space `X`. -/
structure BM (Θ X : Type*) [MeasurableSpace X] where
  /-- Energy functional `E_θ(x)`. -/
  energy : Θ → X → ℝ

namespace BM

variable {Θ X : Type*} [MeasurableSpace X]

section Phases

variable {Vis : Type*} [MeasurableSpace Vis]

/-- Positive phase: data on visibles, then clamp into full configurations. -/
noncomputable def positivePhase (μ_data : Measure Vis) (κ_clamp : Kernel Vis X) : Measure X :=
  μ_data.bind κ_clamp

/-- Negative phase: model equilibrium measure on configurations. -/
abbrev negativePhase (μ_model : Measure X) : Measure X := μ_model

end Phases

section Stats

/-- Real-valued statistic on configurations. -/
abbrev Stat (X : Type*) [MeasurableSpace X] := X → ℝ

/-- Expectation `∫ f dμ` of a statistic under a measure. -/
noncomputable def expectation (μ : Measure X) (f : Stat X) : ℝ :=
  ∫ x, f x ∂μ

/-- BM learning rule: contrastive statistic expectations. -/
structure LearningRule (Θ : Type*) (X : Type*) [MeasurableSpace X] where
  /-- Update direction from positive and negative phase measures. -/
  updateDir : Measure X → Measure X → Θ
  /-- Index type for sufficient-statistic coordinates. -/
  I : Type*
  /-- Sufficient statistics `φ_i : X → ℝ`. -/
  stat : I → Stat X
  /-- Read coordinate `i` from the update vector. -/
  coord : Θ → I → ℝ
  /-- Coordinates match contrastive statistic expectations. -/
  correct :
    ∀ (pos neg : Measure X) (i : I),
      coord (updateDir pos neg) i = expectation pos (stat i) - expectation neg (stat i)

end Stats

end BM

end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
