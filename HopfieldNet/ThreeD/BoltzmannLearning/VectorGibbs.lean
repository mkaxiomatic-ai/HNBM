/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbs

/-!
Legacy re-export of the vector-parameter Gibbs core.

Canonical home: `HopfieldNet.BoltzmannLearningQuiver.VectorGibbs`.
-/

namespace NeuralNetwork

namespace ThreeD

namespace BoltzmannLearning

namespace VectorGibbs

export NeuralNetwork.BoltzmannLearningQuiver.VectorGibbs (
  energy weight Z Z_pos Z_ne_zero num expectation
  hasFDerivAt_weight hasFDerivAt_Z hasGradientAt_logZ)

end VectorGibbs

end BoltzmannLearning

end ThreeD

end NeuralNetwork
