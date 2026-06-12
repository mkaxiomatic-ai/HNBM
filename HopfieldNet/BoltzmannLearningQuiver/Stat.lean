/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.ZeroOne
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Physlib.Thermodynamics.Temperature.Basic

/-!
# Sufficient statistics and flat parameter space (`{0,1}` convention)

Weight statistics are Ackley-style correlations `a_i a_j`; parameters embed `w/2` so that
`hamiltonian = -⟪stat, thetaFromParams⟫`.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace ZeroOne

open scoped BigOperators Temperature
open InnerProductSpace Matrix TwoState VectorGibbs

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Index set for weight and bias coordinates. -/
abbrev I (U : Type) := U × U ⊕ U

/-- Flat parameter Hilbert space `Θ = ℝ^{I(U)}`. -/
abbrev Θ (U : Type) := EuclideanSpace ℝ (I U)

/-- Sufficient statistic: weight coords `a_i a_j`, bias coords `-a_i`. -/
noncomputable def stat (s : State ℝ U) : Θ U :=
  WithLp.toLp 2 (V := I U → ℝ) fun
    | Sum.inl (i, j) => s.act i * s.act j
    | Sum.inr i      => - s.act i

/-- Embed quiver parameters; weight coords store `w_{ij}/2` for energy consistency. -/
noncomputable def thetaFromParams (p : Params ℝ U) : Θ U :=
  WithLp.toLp 2 (V := I U → ℝ) fun
    | Sum.inl (i, j) => (p.w i j) / 2
    | Sum.inr i      => (p.θ i).get fin0

/-- Inverse-temperature-scaled parameter vector. -/
noncomputable def scaledTheta (T : Temperature) (p : Params ℝ U) : Θ U :=
  (-(T.β : ℝ)) • thetaFromParams p

/-- Coordinate statistic `φ_i(s)`. -/
noncomputable def statCoord (i : I U) (s : State ℝ U) : ℝ :=
  (WithLp.ofLp (stat s)) i

/-- Read coordinate `i` from a parameter vector. -/
def coord (θ : Θ U) (i : I U) : ℝ :=
  (WithLp.ofLp θ) i

end ZeroOne
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
