import HopfieldNet.ThreeD.BoltzmannLearning.Core
import HopfieldNet.ThreeD.BoltzmannLearning.FiniteGibbs
import HopfieldNet.ThreeD.BoltzmannLearning.VectorGibbs
import HopfieldNet.ThreeD.BoltzmannLearning.VectorGibbsLearning
import HopfieldNet.ThreeD.BoltzmannLearning.ZeroOneInstantiation
import HopfieldNet.ThreeD.BoltzmannLearning.ZeroOneLearning
import HopfieldNet.ThreeD.BoltzmannLearning.ZeroOneLearningRule
import HopfieldNet.ThreeD.BoltzmannLearning.OptlibBridge

/-!
## ThreeD Boltzmann Machine Learning (legacy entrypoint)

Measure-theoretic BM learning on `Config U = U → Bool` with `{0,1}` activations
(`ZeroOneInstantiation`).

**Canonical quiver development:** `HopfieldNet.BoltzmannLearningQuiver` / `lake build HopfieldNet.BMLearning`.

`TwoStateBridge.lean` is optional (requires `Physlib`) and is not imported here.
-/
