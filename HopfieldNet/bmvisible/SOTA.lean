/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.bmvisible.Partition
import HopfieldNet.bmvisible.Network
import HopfieldNet.bmvisible.Clamp
import HopfieldNet.bmvisible.Dynamics
import HopfieldNet.bmvisible.Bridge
import HopfieldNet.bmvisible.Phases
import HopfieldNet.bmvisible.GibbsStationary
import HopfieldNet.bmvisible.SequentialSweep
import HopfieldNet.bmvisible.SequentialSweepUnique
import HopfieldNet.bmvisible.DynamicsEquivalence
import HopfieldNet.bmvisible.ContrastiveDivergence
import HopfieldNet.bmvisible.CDConvergence
import HopfieldNet.bmvisible.Energy
import HopfieldNet.bmvisible.BoltzmannBridge
import HopfieldNet.bmvisible.Learning

/-!
# Visible/hidden Boltzmann machines (`HopfieldNet.bmvisible`)

Build: `lake build HopfieldNet.BMVisible`

Flagship theorems (see module docs in imported files):

* `negativePhaseMeasure_is_gibbs_stationary`
* `sequentialSweepKernel_invariant_negativePhase`
* `sequentialSweep_uniqueStationaryVec_of_fullSweep`
* `cdNegativePMF_apply_eq_distributionAtTime`
* `cdLearningDirection_tendsto_learningDirection`
* `exactLearningDirection_eq_learningDirection`
* `hasGradientAt_negLogLik_scaled`, `convexOn_negLogLik`, `negLogLik_descent_step_scaled`
* `cdLearningDirection` / `cdLearningDirection_full` (paper CD-$k$ variants)
-/

namespace BMVisible

end BMVisible

#lint only docBlame
