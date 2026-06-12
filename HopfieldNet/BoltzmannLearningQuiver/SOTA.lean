/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.BoltzmannLearningQuiver.Core
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbs
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbsLearning
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbsConvexity
import HopfieldNet.BoltzmannLearningQuiver.VectorGibbsDescent
import HopfieldNet.BoltzmannLearningQuiver.ZeroOne
import HopfieldNet.BoltzmannLearningQuiver.Stat
import HopfieldNet.BoltzmannLearningQuiver.Energy
import HopfieldNet.BoltzmannLearningQuiver.Learning
import HopfieldNet.BoltzmannLearningQuiver.Phases
import HopfieldNet.BoltzmannLearningQuiver.LearningRule
import HopfieldNet.BoltzmannLearningQuiver.Dynamics
import HopfieldNet.BoltzmannLearningQuiver.BoltzmannBridge
import HopfieldNet.BoltzmannLearningQuiver.GibbsStationary
import HopfieldNet.BoltzmannLearningQuiver.SequentialSweep
import HopfieldNet.BoltzmannLearningQuiver.SequentialSweepUnique
import HopfieldNet.BoltzmannLearningQuiver.OptlibBridge
import HopfieldNet.BoltzmannLearningQuiver.ContrastiveDivergence
import HopfieldNet.BoltzmannLearningQuiver.DynamicsEquivalence
import HopfieldNet.BoltzmannLearningQuiver.CDConvergence

/-!
# Boltzmann learning on quiver neural networks

Build: `lake build HopfieldNet.BMLearning`

Flagship theorems:
* `Learning.hasGradientAt_negLogLik_scaled`
* `GibbsStationary.negativePhaseMeasure_is_gibbs_stationary`
* `SequentialSweep.sequentialSweepKernel_invariant_negativePhase`
* `SequentialSweepUnique.sequentialSweep_uniqueStationaryVec_of_fullSweep`
* `CDConvergence.cdLearningDirection_tendsto_exactLearningDirection`
* `Learning.convexOn_negLogLik`, `Learning.negLogLik_descent_step_scaled`

Legacy: `HopfieldNet.ThreeD.BoltzmannLearning.SOTA` (`ZeroOneInstantiation`).
-/

#lint only docBlame docBlameThm
