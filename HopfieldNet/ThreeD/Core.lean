import Mathlib.Probability.Kernel.Basic

/-!
## ThreeD core vocabulary (state × energy × dynamics)

This folder is the “meet point” for the 3 orthogonal axes:

- **Architecture / deterministic dynamics** (MCNN, quivers, update schedules)
- **Stochastic dynamics** (MCMC kernels, Gibbs specifications)
- **Energy / objective** (Hopfield energy, spin-glass Hamiltonians, loss functions)

We keep this file intentionally small: it defines the shared *shapes* (structures) that the
other developments can map into, without forcing a single concrete model.
-/

namespace NeuralNetwork

namespace ThreeD

/-! ### Energy models -/

/-| Unparameterized energy / potential on a state space `X`. -/
structure EnergyModel (X : Type*) where
  energy : X → ℝ

/-| Parameterized energy \(E : Θ → X → ℝ\). -/
structure ParamEnergyModel (Θ X : Type*) where
  energy : Θ → X → ℝ

/-! ### Deterministic dynamics -/

/-| Deterministic dynamics on `X` with parameters `Θ`: one step `X → X`. -/
structure DeterministicDynamics (Θ X : Type*) where
  step : Θ → X → X

namespace DeterministicDynamics

/-| Iterate the step function `k` times. -/
def iterate {Θ X : Type*} (D : DeterministicDynamics Θ X) (θ : Θ) : ℕ → X → X
  | 0 => fun x => x
  | n+1 => fun x => D.step θ (iterate D θ n x)

end DeterministicDynamics

/-! ### Stochastic dynamics (Markov kernels) -/

open ProbabilityTheory

/-| A parameterized stochastic **channel** `X ⟶ₖ Y` (kernels are not required to be endomaps). -/
structure StochasticChannel (Θ X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  K : Θ → Kernel X Y

/-| Stochastic dynamics on `X` parameterized by `Θ`, expressed as a Markov kernel `X ⟶ₖ X`. -/
structure StochasticDynamics (Θ X : Type*) [MeasurableSpace X] where
  K : Θ → Kernel X X

/-!
### Indexed stochastic dynamics

Georgii/DLR-style Gibbs specifications are naturally *indexed* by finite volumes `Λ : Finset S`,
giving a family of boundary-condition kernels `γ Λ`.

This structure is the shared shape for those objects in the ThreeD vocabulary.
-/
structure IndexedStochasticDynamics (ι Θ X : Type*) [MeasurableSpace X] where
  K : ι → Θ → Kernel X X

end ThreeD

end NeuralNetwork
