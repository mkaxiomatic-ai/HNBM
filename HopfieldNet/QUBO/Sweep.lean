/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.QUBO.Minimizers

/-!
# The single-site sweep is HNBM's `Up`

`CNS.Refine` shows the executable net input is HNBM's local field, one neuron at a time. This
module lifts that to the update itself: a memoryless single-site step on the bit array *is*
`NeuralNetwork.State.Up` of `netParams`, and a scan over a list of sites is
`NeuralNetwork.State.workPhase`.

That is the last link in the provenance chain. `CNS.Minimizers` proves things about states of
`TwoState.ZeroOne ℝ (Fin nvars)` evolving by `Up`; this module says the array the executable
sweeps produce is the same object.

## Which dynamics this is about, exactly

`Dynamics.seqRun` carries the momentum accumulator of eqs (3) and (6) — `u ← u + (Wx − θ)` —
even in its asynchronous mode. An accumulator is not an `Up` of any network, and no convergence
theory covers it (see the note in `CNS.Minimizers`). `stepAt` below is the *memoryless* reading:
the neuron is set from the current local field alone. That is the variant `CNS.Minimizers`
describes, and the one this refinement connects to the library.

## The tie

`stepAt` fires on local field `≥ 0`, matching `ZeroOne.fact`, whereas the paper's `σ` of eq. (2)
fires on `> 0`. The two differ only when the field is exactly zero
(`Refine.gt_zero_eq_le_of_ne_zero`). `stepAt` takes HNBM's convention because the point here is
to *be* the library's update, not to be the paper's.
-/

namespace QUBO
namespace Problem

open Finset

variable (P : Problem)

/-! ## One memoryless single-site update -/

/-- Set neuron `u` from the current local field, with no momentum.

`netVec` computes `(Wx̂)_u − θ̂_u` (`Refine.netVec_eq_localField`), so this is exactly
`ZeroOne`'s threshold rule at `u`. -/
def stepAt (x : Array Bool) (u : Nat) : Array Bool :=
  x.set! u (decide (0 ≤ (P.netVec x).getD u 0))

@[simp] theorem stepAt_size (x : Array Bool) (u : Nat) : (P.stepAt x u).size = x.size := by
  unfold stepAt; simp

/-- Reading a site after an update. -/
private theorem stepAt_getD {x : Array Bool} {u : Nat} (hu : u < x.size) (v : Nat) :
    (P.stepAt x u).getD v false
      = if v = u then decide (0 ≤ (P.netVec x).getD u 0) else x.getD v false := by
  unfold stepAt
  by_cases h : v = u
  · subst h
    rw [if_pos rfl]
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hu]
    rfl
  · rw [if_neg h]
    simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne (Ne.symm h)]

variable [Nonempty (Fin P.nvars)]

/-- **One executable step is one `NeuralNetwork.State.Up`.** -/
theorem stateOfBits_stepAt (hW : P.Wf) {x : Array Bool} (hx : x.size = P.nvars)
    (u : Fin P.nvars) :
    stateOfBits P (bitsOf P (P.stepAt x u.val))
      = (stateOfBits P (bitsOf P x)).Up (netParams P) u := by
  have hu : u.val < x.size := by rw [hx]; exact u.isLt
  refine NeuralNetwork.ext fun v => ?_
  show bit (bitsOf P (P.stepAt x u.val) v) = _
  have hRHS : ((stateOfBits P (bitsOf P x)).Up (netParams P) u).act v
      = if v = u then
          (if ((netParams P).θ u).get TwoState.fin0
              ≤ (stateOfBits P (bitsOf P x)).net (netParams P) u then (1 : ℝ) else 0)
        else bit (bitsOf P x v) := rfl
  have hb : ∀ (y : Array Bool) (w : Fin P.nvars), bitsOf P y w = y.getD w.val false :=
    fun _ _ => rfl
  rw [hRHS, hb, stepAt_getD P hu v.val]
  by_cases h : v = u
  · subst h
    rw [if_pos rfl, if_pos rfl]
    -- the threshold test and the sign of `netVec` are the same test
    have hlf := netVec_eq_localField P hW x v
    unfold bit
    by_cases hle : ((netParams P).θ v).get TwoState.fin0
        ≤ (stateOfBits P (bitsOf P x)).net (netParams P) v
    · have hz : (0 : Int) ≤ (P.netVec x).getD v.val 0 := by
        have : (0 : ℝ) ≤ ((P.netVec x).getD v.val 0 : ℝ) := by rw [hlf]; linarith
        exact_mod_cast this
      rw [if_pos hle, if_pos (by simpa using hz)]
    · have hz : ¬ (0 : Int) ≤ (P.netVec x).getD v.val 0 := by
        intro hc
        have : (0 : ℝ) ≤ ((P.netVec x).getD v.val 0 : ℝ) := by exact_mod_cast hc
        rw [hlf] at this
        exact hle (by linarith)
      rw [if_neg hle, if_neg (by simpa using hz)]
  · have hne : v.val ≠ u.val := fun hc => h (Fin.ext hc)
    rw [if_neg hne, if_neg h, hb]

/-! ## A scan over many sites -/

/-- **A scan of memoryless single-site updates is `NeuralNetwork.State.workPhase`.**

The executable sweep over a list of neurons and the library's fold of `Up` over the same list
produce the same state. With `CNS.Minimizers`, that makes the objective the sweep descends the
one whose minimisers are the solved grids. -/
theorem stateOfBits_foldl (hW : P.Wf) :
    ∀ (us : List (Fin P.nvars)) {x : Array Bool}, x.size = P.nvars →
      stateOfBits P (bitsOf P (us.foldl (fun x u => P.stepAt x u.val) x))
        = us.foldl (fun s u => s.Up (netParams P) u) (stateOfBits P (bitsOf P x)) := by
  intro us
  induction us with
  | nil => intro x _; rfl
  | cons u t ih =>
    intro x hx
    rw [List.foldl_cons, List.foldl_cons, ← stateOfBits_stepAt P hW hx u,
      ih (by rw [stepAt_size]; exact hx)]

/-- The same statement as `workPhase`, the library's own name for the scan. -/
theorem stateOfBits_workPhase (hW : P.Wf) (us : List (Fin P.nvars))
    {x : Array Bool} (hx : x.size = P.nvars)
    (h0 : (stateOfBits P (bitsOf P x)).onlyUi) :
    stateOfBits P (bitsOf P (us.foldl (fun x u => P.stepAt x u.val) x))
      = NeuralNetwork.State.workPhase (netParams P) (stateOfBits P (bitsOf P x)) h0 us :=
  stateOfBits_foldl P hW us hx

end Problem
end QUBO
