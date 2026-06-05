import HopfieldNet.BoltzmannLearningQuiver.Core
import HopfieldNet.BoltzmannLearningQuiver.SymmetricBinary
import HopfieldNet.BoltzmannLearningQuiver.Stat
import HopfieldNet.BoltzmannLearningQuiver.Energy
import HopfieldNet.BoltzmannLearningQuiver.Learning
import HopfieldNet.BoltzmannLearningQuiver.Phases
import HopfieldNet.BoltzmannLearningQuiver.LearningRule
import HopfieldNet.BoltzmannLearningQuiver.Dynamics
import HopfieldNet.BoltzmannLearningQuiver.BoltzmannBridge

/-!
## Boltzmann learning on Quiver neural networks — entry surface

Build: `lake build HopfieldNet.BoltzmannLearningQuiver`

Architecture:
- **Core:** `HopfieldNet.Quiver.NeuralNetwork` (`SymmetricBinary`, `Params`, `State`)
- **Energy / Gibbs:** `HopfieldEnergy`, `HopfieldBoltzmann`, `Ergodicity`
- **Learning:** `VectorGibbsLearning` gradient identities on Quiver states
-/
