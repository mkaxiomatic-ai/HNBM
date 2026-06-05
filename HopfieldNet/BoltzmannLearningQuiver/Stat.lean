/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.SymmetricBinary
import HopfieldNet.ThreeD.BoltzmannLearning.VectorGibbs
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
## Sufficient statistics and parameter vector on Quiver states

Features are read directly from `(SymmetricBinary R U).State`, matching the Hopfield
Hamiltonian in `HopfieldEnergy.hamiltonian`.
-/

namespace NeuralNetwork

namespace BoltzmannLearningQuiver

namespace SymmetricBinary

open scoped BigOperators
open InnerProductSpace Matrix TwoState

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Index set for weight and bias coordinates. -/
abbrev I (U : Type) := U × U ⊕ U

/-- Flat parameter space for vector-parameter Gibbs / gradient identities. -/
abbrev Θ (U : Type) := EuclideanSpace ℝ (I U)

/-- Sufficient statistic `φ(s)` for a Quiver state `s` (pairwise products and biases). -/
noncomputable def stat (s : State ℝ U) : Θ U :=
  WithLp.toLp 2 (V := I U → ℝ) fun
    | Sum.inl (i, j) => (1 / 2 : ℝ) * s.act i * s.act j
    | Sum.inr i      => - s.act i

/-- Embed Quiver `Params` into the flat vector `θ`. -/
noncomputable def thetaFromParams (p : Params ℝ U) : Θ U :=
  WithLp.toLp 2 (V := I U → ℝ) fun
    | Sum.inl (i, j) => p.w i j
    | Sum.inr i      => (p.θ i).get fin0

end SymmetricBinary

end BoltzmannLearningQuiver

end NeuralNetwork
