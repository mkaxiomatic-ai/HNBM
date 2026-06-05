import HopfieldNet.BoltzmannLearningQuiver.SOTA

/-!
## Boltzmann learning with Quiver as core

Unlike `HopfieldNet.BMLearning` (ThreeD, self-contained), this entrypoint builds BM learning
directly on `HopfieldNet.Quiver.NeuralNetwork` states, parameters, energies, and Gibbs dynamics.

Build: `lake build HopfieldNet.BoltzmannLearningQuiver`
-/
