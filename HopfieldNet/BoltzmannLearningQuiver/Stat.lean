/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.SymmetricBinary
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Physlib.Thermodynamics.Temperature.Basic

/-!
# Sufficient statistics and flat parameter space

`stat`, `thetaFromParams`, and temperature-scaled `scaledTheta T p`.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace SymmetricBinary

open scoped BigOperators Temperature
open InnerProductSpace Matrix TwoState VectorGibbs

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- Index set for weight and bias coordinates. -/
abbrev I (U : Type) := U × U ⊕ U

/-- Flat parameter Hilbert space `Θ = ℝ^{I(U)}`. -/
abbrev Θ (U : Type) := EuclideanSpace ℝ (I U)

/-- Sufficient statistic for a quiver state. -/
noncomputable def stat (s : State ℝ U) : Θ U :=
  WithLp.toLp 2 (V := I U → ℝ) fun
    | Sum.inl (i, j) => (1 / 2 : ℝ) * s.act i * s.act j
    | Sum.inr i      => - s.act i

/-- Embed quiver `Params` into flat `Θ U`. -/
noncomputable def thetaFromParams (p : Params ℝ U) : Θ U :=
  WithLp.toLp 2 (V := I U → ℝ) fun
    | Sum.inl (i, j) => p.w i j
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

end SymmetricBinary
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
