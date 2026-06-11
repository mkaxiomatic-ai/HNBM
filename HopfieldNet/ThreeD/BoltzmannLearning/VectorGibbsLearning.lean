/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.ThreeD.BoltzmannLearning.VectorGibbs
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbsLearning

/-!
Legacy re-export of vector-parameter Gibbs learning identities.

Canonical home: `HopfieldNet.BoltzmannLearningQuiver.VectorGibbsLearning`.
-/

namespace NeuralNetwork

namespace ThreeD

namespace BoltzmannLearning

namespace VectorGibbs

export NeuralNetwork.BoltzmannLearningQuiver.VectorGibbs (negLogLik hasGradientAt_negLogLik)

end VectorGibbs

end BoltzmannLearning

end ThreeD

end NeuralNetwork
