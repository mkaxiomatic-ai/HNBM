import HopfieldNet.ThreeD.Core
import HopfieldNet.ThreeD.Invariant
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
## Boltzmann Machine learning (Ackley–Hinton–Sejnowski 1985): core, nontrivial definitions

This module is designed to integrate the BM learning paper by implementing the following design choices:

- never using informal “probabilities” `p_ij` as raw numbers without stating the ambient measure;
- keeping **positive phase** (clamped/data) and **negative phase** (free-running/model) as explicit measures;
- phrasing learning as a statement about **expectations of sufficient statistics** under those measures.

We intentionally separate:

- **Definitions** (this file)
- **Theorems** (gradient of KL / logZ and the classic learning rule)

This keeps the formalization deep and audit-friendly: every symbol has a type and a scope.
-/

namespace NeuralNetwork

namespace ThreeD

namespace BoltzmannLearning

open ProbabilityTheory MeasureTheory

/-! ### Binary state conventions -/

/-- A binary unit state, as used in the original BM paper. -/
abbrev Bit := Bool

/-- The numeric interpretation used by the paper: `s ∈ {0,1}`. -/
def bit01 : Bit → ℝ := fun b => if b then 1 else 0

/-! ### Configuration spaces -/

variable (U : Type*)   -- units
variable (V : Type*)   -- visible interface (can be a subtype or an external “visible state type”)

/-- A full network configuration assigns a bit to each unit. -/
abbrev Config (U : Type*) := U → Bit

/-!
### Core BM model as an energy-based generative model

We model the “free-running” distribution as a Gibbs measure on the full configuration space.
The *learning* problem is then about matching a target distribution on visibles, typically by
minimizing a divergence, whose gradient becomes a difference of expectations.
-/

structure BM (Θ : Type*) (U : Type*) where
  /-- Energy function \(E_θ(x)\) on full configurations. Temperature can be baked into `energy`. -/
  energy : Θ → Config U → ℝ

namespace BM

variable {Θ : Type*} {U : Type*}

/-!
### Positive vs negative phase, defined as measures

We do **not** hard-code a particular clamping mechanism here. Instead we parameterize it by:

- a measure on visible states (data distribution)
- a kernel that extends/clamps a visible state into a distribution on full configurations

This matches the paper’s semantics (“clamp visibles then equilibrate hiddens”) while remaining
agnostic about the specific equilibration algorithm (Gibbs, MH, mean-field, etc.).
-/

section Phases

variable {Vis : Type*} [MeasurableSpace Vis]
variable [MeasurableSpace (Config U)]

/-- Positive phase: data on visibles + a conditional kernel to full states gives a joint measure on configs. -/
noncomputable def positivePhase (μ_data : Measure Vis) (κ_clamp : Kernel Vis (Config U)) : Measure (Config U) :=
  μ_data.bind κ_clamp

/-- Negative phase: a model equilibrium measure on configs (e.g. Gibbs at temperature T). -/
abbrev negativePhase (μ_model : Measure (Config U)) : Measure (Config U) := μ_model

end Phases

/-! ### Sufficient statistics and learning rule interface -/

section Stats

variable {U : Type*}

/-- A real-valued statistic on configurations (e.g. pairwise correlation). -/
abbrev Stat (U : Type*) := Config U → ℝ

variable [MeasurableSpace (Config U)]

/-- Expectation of a statistic under a (finite) measure. -/
noncomputable def expectation (μ : Measure (Config U)) (f : Stat U) : ℝ :=
  ∫ x, f x ∂μ

/-|
The *BM learning rule schema*:

For each parameter component (e.g. weight `w_ij` or bias `b_i`), pick a corresponding statistic `φ`.
Then the “canonical” update direction is:

`E_pos[φ] - E_neg[φ]`.

We bundle this as a map `Θ → Θ` supplied by the user, together with the statement that it matches
this expectation-difference pattern for the chosen statistics.

This is the right place to later prove the theorem “this equals the gradient of KL / log-likelihood”
under explicit hypotheses.
-/
structure LearningRule (Θ : Type*) (U : Type*) where
  /-- Update direction (to be used by an optimizer/step size controller). -/
  updateDir : (pos neg : Measure (Config U)) → Θ
  /-- The chosen sufficient statistics indexed by parameter components (abstract index set `I`). -/
  (I : Type*)
  stat : I → Stat U
  /-- Interpretation of an update direction coordinate-wise. -/
  coord : Θ → I → ℝ
  /-- The rule is the difference of expectations for all stats. -/
  correct :
    ∀ (pos neg : Measure (Config U)),
      (∀ i, coord (updateDir pos neg) i = expectation pos (stat i) - expectation neg (stat i))

end Stats

end BM

end BoltzmannLearning

end ThreeD

end NeuralNetwork
