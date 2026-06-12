import HopfieldNet.ThreeD.BoltzmannLearning.Core
import HopfieldNet.ThreeD.BoltzmannLearning.VectorGibbsLearning
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Block

/-!
## Concrete instantiation: `{0,1}` Boltzmann energy as a vector-parameter Gibbs model

Connects a `{0,1}` Boltzmann Hamiltonian to the abstract finite vector-parameter Gibbs layer
(`VectorGibbs` / `VectorGibbsLearning`).

Self-contained parameter bundle `Params` (no `Physlib` required). Sufficient statistics use
Ackley-style correlations `a_i a_j`:

`hopfieldEnergy p c = VectorGibbs.energy stat thetaOfParams c = -⟪stat c, thetaFromParams p⟫`,

matching `HopfieldEnergy.zeroOneHamiltonian` in `HopfieldNet.Quiver.BM.BoltzmannMachine`.
-/

namespace NeuralNetwork
namespace ThreeD
namespace BoltzmannLearning

open scoped BigOperators
open InnerProductSpace
open Matrix

namespace ZeroOneInstantiation

noncomputable section

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Boltzmann parameters: symmetric weights and scalar biases. -/
structure Params where
  w : Matrix U U ℝ
  bias : U → ℝ

/-- Activation value of a Bool configuration (`true ↦ 1`, `false ↦ 0`). -/
def activation (c : Config U) (u : U) : ℝ :=
  if c u then (1 : ℝ) else (0 : ℝ)

abbrev Θ (U : Type) := EuclideanSpace ℝ (U × U ⊕ U)

/-- Sufficient statistics: weight coords `a_i a_j`, bias coords `-a_i`. -/
noncomputable def stat (c : Config U) : Θ U :=
  WithLp.toLp 2 (V := (U × U ⊕ U) → ℝ) fun
    | Sum.inl (i, j) => activation (U := U) c i * activation (U := U) c j
    | Sum.inr i      => - activation (U := U) c i

/-- Flat parameters; weight coords store `w_{ij}/2` for energy consistency. -/
noncomputable def thetaFromParams (p : Params (U := U)) : Θ U :=
  WithLp.toLp 2 (V := (U × U ⊕ U) → ℝ) fun
    | Sum.inl (i, j) => (p.w i j) / 2
    | Sum.inr i      => p.bias i

/-- Gibbs / Boltzmann energy packaged as `-⟪stat, θ⟫`. -/
noncomputable def hopfieldEnergy (p : Params (U := U)) (c : Config U) : ℝ :=
  VectorGibbs.energy (X := Config U) (Θ := Θ U) (stat := stat (U := U)) (thetaFromParams (U := U) p) c

theorem hopfieldEnergy_eq_vectorGibbs_energy
    (p : Params (U := U)) (c : Config U) :
    hopfieldEnergy (U := U) p c
      =
    VectorGibbs.energy (X := Config U) (Θ := Θ U) (stat := stat (U := U)) (thetaFromParams (U := U) p) c :=
  rfl

alias hamiltonian_eq_vectorGibbs_energy := hopfieldEnergy_eq_vectorGibbs_energy

/-- Explicit `{0,1}` Hamiltonian packaged as Gibbs energy. -/
noncomputable abbrev hopfieldHamiltonian (p : Params (U := U)) (c : Config U) : ℝ :=
  hopfieldEnergy (U := U) p c

theorem hopfieldEnergy_eq_hopfieldHamiltonian
    (p : Params (U := U)) (c : Config U) :
    hopfieldEnergy (U := U) p c = hopfieldHamiltonian (U := U) p c :=
  rfl

end

end ZeroOneInstantiation

end BoltzmannLearning
end ThreeD
end NeuralNetwork
