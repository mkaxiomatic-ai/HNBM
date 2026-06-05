/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.SymmetricBinary
import HopfieldNet.Quiver.BM.Ergodicity

/-!
## Gibbs dynamics on Quiver states (hooks for CD / truncated negative phase)

Re-exports the Quiver two-state Gibbs update and points to the ergodicity layer
showing unique convergence to the Boltzmann stationary distribution.
-/

namespace NeuralNetwork

namespace BoltzmannLearningQuiver

namespace SymmetricBinary

open TwoState HopfieldEnergy

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-- One-site Gibbs update at neuron `u` (Quiver `TwoState` kernel). -/
noncomputable abbrev gibbsUpdate {F} [FunLike F ℝ ℝ] (f : F) (p : Params ℝ U) (T : Temperature)
    (s : State ℝ U) (u : U) : PMF (State ℝ U) :=
  TwoState.gibbsUpdate (R := ℝ) (U := U) (ζ := ℝ) (NN := NN ℝ U) f p T s u

/-- Sequential Gibbs sweep over a list of sites (head applied first). -/
noncomputable abbrev gibbsSweep {F} [FunLike F ℝ ℝ] (order : List U) (p : Params ℝ U)
    (T : Temperature) (f : F) (s0 : State ℝ U) : PMF (State ℝ U) :=
  TwoState.gibbsSweep (R := ℝ) (U := U) (ζ := ℝ) (NN := NN ℝ U) order p T f s0

-- Random-scan Gibbs kernel ergodicity: see HopfieldNet.Quiver.BM.Ergodicity.

end SymmetricBinary

end BoltzmannLearningQuiver

end NeuralNetwork
