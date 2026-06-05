import HopfieldNet.ThreeD.BoltzmannLearning.Core
import HopfieldNet.ThreeD.BoltzmannLearning.FiniteGibbs
import HopfieldNet.ThreeD.BoltzmannLearning.VectorGibbs
import HopfieldNet.ThreeD.BoltzmannLearning.VectorGibbsLearning
import HopfieldNet.ThreeD.BoltzmannLearning.SymmetricBinaryInstantiation
import HopfieldNet.ThreeD.BoltzmannLearning.SymmetricBinaryLearning
import HopfieldNet.ThreeD.BoltzmannLearning.SymmetricBinaryLearningRule
import HopfieldNet.ThreeD.BoltzmannLearning.OptlibBridge

/-!
## ThreeD Boltzmann Machine Learning: SOTA entrypoint

Import surface for the BM learning layer (Ackley–Hinton–Sejnowski 1985), formalized in a
measure-theoretic style with verified Gibbs gradient identities and a Hopfield instantiation.

Build: `lake build HopfieldNet.BMLearning`

Note: `TwoStateBridge.lean` is optional (requires `Physlib`) and is not imported here.
-/
