/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.bmvisible.Network

/-!
# Clamping visible units to a pattern

A **visible pattern** fixes activations on `U_vis`. Hidden units are initialised to `0`
before a hidden-only Gibbs sweep in the positive phase.
-/

namespace BMVisible

open NeuralNetwork TwoState

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype U] [DecidableEq U] [Nonempty U]

/-- Activations on visible units only (`{0,1}`). -/
structure VisiblePattern {U : Type} [Fintype U] [DecidableEq U] {R : Type} [Field R]
    (part : VisibleHiddenPartition U) where
  /-- Activation on visible unit `u`. -/
  act : ∀ u ∈ part.visible, R
  /-- Each visible activation lies in `{0,1}`. -/
  hp : ∀ u (hu : u ∈ part.visible), act u hu = 0 ∨ act u hu = 1

/-- Extend a visible pattern to a full network state (hidden units start at `0`). -/
noncomputable def visiblePatternToState (part : VisibleHiddenPartition U)
    (vp : VisiblePattern (R := R) part) : BMState (R := R) (U := U) part :=
  { act := fun u =>
      if hu : u ∈ part.visible then vp.act u hu else (0 : R)
    hp := by
      intro u
      by_cases hu : u ∈ part.visible
      · simpa [hu] using vp.hp u hu
      · simp [hu, ZeroOneVisibleHidden, ZeroOne, SymmetricBinary] }

/-- Replace visible coordinates; leave hidden coordinates unchanged. -/
def visiblePatternMergeInto (part : VisibleHiddenPartition U) (vp : VisiblePattern (R := R) part)
    (s : BMState (R := R) (U := U) part) : BMState (R := R) (U := U) part :=
  { act := fun u =>
      if hu : u ∈ part.visible then vp.act u hu else s.act u
    hp := by
      intro u
      by_cases hu : u ∈ part.visible
      · simpa [hu] using vp.hp u hu
      · simpa [hu] using s.hp u }

/-- Visible coordinates agree with the pattern. -/
lemma visiblePatternToState_act_vis (part : VisibleHiddenPartition U)
    (vp : VisiblePattern (R := R) part) (u : U) (hu : u ∈ part.visible) :
    (visiblePatternToState part vp).act u = vp.act u hu := by
  simp [visiblePatternToState, hu]

/-- Hidden coordinates are zero in the extension. -/
lemma visiblePatternToState_act_hidden (part : VisibleHiddenPartition U)
    (vp : VisiblePattern (R := R) part) (u : U) (hu : u ∈ hidSet part) :
    (visiblePatternToState part vp).act u = (0 : R) := by
  simp [visiblePatternToState]
  have hvis : u ∉ part.visible := not_mem_visSet part hu
  simp [hvis]

end BMVisible

#lint only docBlame
