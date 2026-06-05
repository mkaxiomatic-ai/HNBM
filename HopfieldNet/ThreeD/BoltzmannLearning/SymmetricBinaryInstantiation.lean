import HopfieldNet.ThreeD.BoltzmannLearning.Core
import HopfieldNet.ThreeD.BoltzmannLearning.VectorGibbsLearning
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Block

/-!
## Concrete instantiation: SymmetricBinary Hopfield energy as a vector-parameter Gibbs model

This file connects a concrete Hopfield Hamiltonian on `{±1}` spins to the abstract finite
vector-parameter Gibbs theorem layer (`VectorGibbs` / `VectorGibbsLearning`).

We use a self-contained parameter bundle `Params` so this module builds independently of
`HopfieldNet.Quiver.NeuralNetwork.TwoState` (which pulls in `Physlib`). The sufficient
statistics are chosen so that

`hopfieldEnergy p c = VectorGibbs.energy stat thetaOfParams c = -⟪stat c, thetaOfParams p⟫`,

which is the same algebra as `HopfieldEnergy.hamiltonian` in `HopfieldNet.Quiver.BM.BoltzmannMachine`.
-/

namespace NeuralNetwork
namespace ThreeD
namespace BoltzmannLearning

open scoped BigOperators
open InnerProductSpace
open Matrix

namespace SymmetricBinaryInstantiation

noncomputable section

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Hopfield/BM parameters: symmetric weights and scalar biases. -/
structure Params where
  w : Matrix U U ℝ
  bias : U → ℝ

/-- Spin value of a Bool configuration (`true ↦ 1`, `false ↦ -1`). -/
def spin (c : Config U) (u : U) : ℝ :=
  if c u then (1 : ℝ) else (-1 : ℝ)

abbrev Θ (U : Type) := EuclideanSpace ℝ (U × U ⊕ U)

noncomputable def stat (c : Config U) : Θ U :=
  WithLp.toLp 2 (V := (U × U ⊕ U) → ℝ) fun
    | Sum.inl (i, j) => (1 / 2 : ℝ) * spin (U := U) c i * spin (U := U) c j
    | Sum.inr i      => - spin (U := U) c i

noncomputable def thetaOfParams (p : Params (U := U)) : Θ U :=
  WithLp.toLp 2 (V := (U × U ⊕ U) → ℝ) fun
    | Sum.inl (i, j) => p.w i j
    | Sum.inr i      => p.bias i

/-- Gibbs / Hopfield energy packaged as `-⟪stat, θ⟫`. -/
noncomputable def hopfieldEnergy (p : Params (U := U)) (c : Config U) : ℝ :=
  VectorGibbs.energy (X := Config U) (Θ := Θ U) (stat := stat (U := U)) (thetaOfParams (U := U) p) c

theorem hopfieldEnergy_eq_vectorGibbs_energy
    (p : Params (U := U)) (c : Config U) :
    hopfieldEnergy (U := U) p c
      =
    VectorGibbs.energy (X := Config U) (Θ := Θ U) (stat := stat (U := U)) (thetaOfParams (U := U) p) c :=
  rfl

/-- Alias matching the HopfieldNet naming convention. -/
alias hamiltonian_eq_vectorGibbs_energy := hopfieldEnergy_eq_vectorGibbs_energy

/-- Explicit Hopfield Hamiltonian on `{±1}` spins: `E = -½ sᵀ W s + bᵀ s`.
    Definitional alias for the Gibbs energy packaging above. -/
noncomputable abbrev hopfieldHamiltonian (p : Params (U := U)) (c : Config U) : ℝ :=
  hopfieldEnergy (U := U) p c

theorem hopfieldEnergy_eq_hopfieldHamiltonian
    (p : Params (U := U)) (c : Config U) :
    hopfieldEnergy (U := U) p c = hopfieldHamiltonian (U := U) p c :=
  rfl

end

end SymmetricBinaryInstantiation

end BoltzmannLearning
end ThreeD
end NeuralNetwork
