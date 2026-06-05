/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.Quiver.NeuralNetwork.Main
import HopfieldNet.Quiver.NeuralNetwork.TwoState
import HopfieldNet.ThreeD.BoltzmannLearning.Core

/-!
## Boltzmann learning on Quiver neural networks

This folder develops BM learning with **`HopfieldNet.Quiver.NeuralNetwork`** as the core:

- states are `NN.State`, parameters are `Params NN`;
- energies come from `HopfieldEnergy` / `EnergySpec'`;
- Gibbs dynamics come from `TwoState.gibbsUpdate` and `HopfieldNet.Quiver.BM`.

The abstract phase / learning-rule vocabulary from `ThreeD.BoltzmannLearning.Core` is reused,
but **instantiated on Quiver state spaces** rather than on a parallel `Config U = U → Bool`.
-/

namespace NeuralNetwork

namespace BoltzmannLearningQuiver

open ThreeD.BoltzmannLearning

end BoltzmannLearningQuiver

end NeuralNetwork
