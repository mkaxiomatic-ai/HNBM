/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.ZeroOne
import HopfieldNet.Quiver.BM.Ergodicity

/-!
# Gibbs dynamics aliases on quiver states

Single-site and sequential Gibbs updates for CD-k sampling.
-/

namespace NeuralNetwork
namespace BoltzmannLearningQuiver
namespace ZeroOne

open TwoState HopfieldEnergy

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- One-site Gibbs update PMF. -/
noncomputable abbrev gibbsUpdate {F} [FunLike F ℝ ℝ] (f : F) (p : Params ℝ U) (T : Temperature)
    (s : State ℝ U) (u : U) : PMF (State ℝ U) :=
  TwoState.gibbsUpdate (R := ℝ) (U := U) (ζ := ℝ) (NN := NN ℝ U) f p T s u

/-- Sequential Gibbs sweep PMF over `order`. -/
noncomputable abbrev gibbsSweep {F} [FunLike F ℝ ℝ] (order : List U) (p : Params ℝ U)
    (T : Temperature) (f : F) (s0 : State ℝ U) : PMF (State ℝ U) :=
  TwoState.gibbsSweep (R := ℝ) (U := U) (ζ := ℝ) (NN := NN ℝ U) order p T f s0

end ZeroOne
end BoltzmannLearningQuiver
end NeuralNetwork

#lint only docBlame docBlameThm
