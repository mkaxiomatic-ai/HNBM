import HopfieldNet.Quiver.NeuralNetwork.Main
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-- Probability Mass Function over Neural Network States -/
def NeuralNetwork.StatePMF {R U ζ : Type} [Zero R]
  (NN : NeuralNetwork R U ζ) := PMF (NN.State)

/-- Temperature-parameterized stochastic dynamics for neural networks -/
def NeuralNetwork.StochasticDynamics {R U ζ : Type} [Zero R]
    (NN : NeuralNetwork R U ζ) :=
  ∀ (_ : ℝ), NN.State → NeuralNetwork.StatePMF NN

-- /-- Metropolis acceptance decision as a probability mass function over Boolean outcomes -/
-- def NN.State.metropolisDecision (p : ℝ) : PMF Bool := by
--   exact PMF.bernoulli (ENNReal.ofReal (min p 1))
--   (mod_cast min_le_right p 1)

/-- Metropolis acceptance decision as a probability mass function over Boolean outcomes -/
def NN.State.metropolisDecision (p : ℝ) : PMF Bool := by
  -- Clamp `p` into `[0,1]` and use it as an `NNReal` parameter for `PMF.bernoulli`.
  let q : NNReal :=
    ⟨min (max p 0) 1, by
      exact le_min (le_max_right _ _) (by simpa using (show (0 : ℝ) ≤ (1 : ℝ) from zero_le_one))⟩
  refine PMF.bernoulli q ?_
  show q ≤ 1
  exact min_le_right (max p 0) 1
