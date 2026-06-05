import HopfieldNet.ThreeD.Core
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Basic

/-!
## ThreeD invariance / stationarity

This file defines “stationarity” for the ThreeD stochastic interfaces.

Key point: in Mathlib, kernel invariance is `μ.bind κ = μ`.
We reuse that directly.
-/

namespace NeuralNetwork

namespace ThreeD

open ProbabilityTheory MeasureTheory

section

variable {X : Type*} [MeasurableSpace X]

/-| A measure `μ` is stationary for a `ThreeD.StochasticDynamics` at parameter `θ`. -/
def IsStationary (D : ThreeD.StochasticDynamics Θ X) (θ : Θ) (μ : Measure X) : Prop :=
  ProbabilityTheory.Kernel.Invariant (D.K θ) μ

/-| A measure `μ` is stationary for an indexed family at parameter `θ`, for all indices. -/
def IsStationaryIndexed (D : ThreeD.IndexedStochasticDynamics ι Θ X) (θ : Θ) (μ : Measure X) : Prop :=
  ∀ i : ι, ProbabilityTheory.Kernel.Invariant (D.K i θ) μ

end

/-! ### Composition of indexed local updates -/

open scoped ProbabilityTheory  -- for `∘ₖ`

section

variable {ι Θ X : Type*} [MeasurableSpace X]

/-- Compose the kernels in a finite list of indices (left-to-right update schedule). -/
noncomputable def kernelOfList (D : ThreeD.IndexedStochasticDynamics ι Θ X) (θ : Θ) :
    List ι → ProbabilityTheory.Kernel X X
  | [] => ProbabilityTheory.Kernel.id
  | i :: is => (kernelOfList D θ is) ∘ₖ (D.K i θ)

@[simp] lemma kernelOfList_nil (D : ThreeD.IndexedStochasticDynamics ι Θ X) (θ : Θ) :
    kernelOfList D θ [] = ProbabilityTheory.Kernel.id := rfl

@[simp] lemma kernelOfList_cons (D : ThreeD.IndexedStochasticDynamics ι Θ X) (θ : Θ) (i : ι) (is : List ι) :
    kernelOfList D θ (i :: is) = (kernelOfList D θ is) ∘ₖ (D.K i θ) := rfl

/-- If `μ` is stationary for every local kernel, it is stationary for any finite composition schedule. -/
theorem IsStationaryIndexed.kernelOfList_invariant
    {D : ThreeD.IndexedStochasticDynamics ι Θ X} {θ : Θ} {μ : Measure X}
    (h : ThreeD.IsStationaryIndexed (D := D) θ μ) :
    ∀ is : List ι, ProbabilityTheory.Kernel.Invariant (kernelOfList D θ is) μ := by
  intro is
  induction is with
  | nil =>
      simp [ProbabilityTheory.Kernel.Invariant, kernelOfList]
  | cons i is ih =>
      have hi : ProbabilityTheory.Kernel.Invariant (D.K i θ) μ := h i
      simpa [kernelOfList] using ProbabilityTheory.Kernel.Invariant.comp (hκ := ih) (hη := hi)

end

end ThreeD

end NeuralNetwork
