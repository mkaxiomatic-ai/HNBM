/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.bmvisible.Partition
import HopfieldNet.Quiver.NeuralNetwork.TwoState

/-!
# Visible/hidden `{0,1}` Boltzmann machine as a `NeuralNetwork`

## Mathematical definition (paper style)

A **Boltzmann machine** is a symmetric fully connected neural network (Definition in §2.4
style) with activations in `{0,1}`, energy
\[
  E(\mathrm{act}) = -\tfrac12 \sum_{u,v} w_{uv}\,\mathrm{act}_u\,\mathrm{act}_v
  + \sum_u \theta_u\,\mathrm{act}_u,
\]
and Gibbs dynamics at temperature `T`.

Relative to the fully visible Hopfield-style instance (`TwoState.ZeroOne`), a **visible/hidden
BM** additionally specifies a partition `U = U_{\mathrm{vis}} \sqcup U_{\mathrm{hid}}`:
visible units carry patterns; hidden units are latent.
In `NeuralNetwork` notation we set `Ui = Uo = U_vis` and `Uh = U_hid`.

Learning (not dynamics) uses this partition: in the **positive phase** visible activations
are held fixed to a presented pattern and only hidden units are updated; in the **negative
phase** all units are updated freely (same full-network Gibbs kernel as §5).
-/

namespace BMVisible

open NeuralNetwork TwoState

/-- `{0,1}` BM with visible/hidden partition. Same connectivity and local functions as
`TwoState.ZeroOne`; only `Ui`/`Uo`/`Uh` differ. -/
def ZeroOneVisibleHidden (R : Type) (U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype U] [DecidableEq U] [Nonempty U] (part : VisibleHiddenPartition U) :
    NeuralNetwork R U R :=
  { (ZeroOne R U) with
    Ui := visSet part
    Uo := visSet part
    Uh := hidSet part
    hU := by
      symm
      rw [Set.union_self, union_vis_hid part]
    hhio := by
      rw [Set.inter_union_distrib_left, Set.union_self, Set.inter_comm]
      exact (disjoint_vis_hid part).inter_eq
    hUi := by
      rw [visSet]
      obtain ⟨u, hu⟩ := part.hvisible_nonempty
      intro h
      have hu' : u ∈ (∅ : Set U) := by simpa [h] using (show u ∈ (↑part.visible : Set U) from hu)
      simp at hu'
    hUo := by
      rw [visSet]
      obtain ⟨u, hu⟩ := part.hvisible_nonempty
      intro h
      have hu' : u ∈ (∅ : Set U) := by simpa [h] using (show u ∈ (↑part.visible : Set U) from hu)
      simp at hu' }

/-- Quiver neural network for this partition. -/
abbrev NN (R : Type) (U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype U] [DecidableEq U] [Nonempty U] (part : VisibleHiddenPartition U) :=
  ZeroOneVisibleHidden R U part

/-- Network state. -/
abbrev BMState (R : Type) (U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype U] [DecidableEq U] [Nonempty U] (part : VisibleHiddenPartition U) :=
  NeuralNetwork.State (NN R U part)

/-- Network parameters. -/
abbrev BMParams (R : Type) (U : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype U] [DecidableEq U] [Nonempty U] (part : VisibleHiddenPartition U) :=
  _root_.Params (NN R U part)

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype U] [DecidableEq U] [Nonempty U]

instance instTwoState (part : VisibleHiddenPartition U) :
    TwoStateNeuralNetwork (NN R U part) where
  ζ_pos := (1 : R)
  ζ_neg := (0 : R)
  h_pos_ne_neg := one_ne_zero
  θ0 := fun _ => fin0
  h_fact_pos := by
    intro u ζcur net θ hn
    change (if θ.get fin0 ≤ net then (1 : R) else 0) = 1
    simp [hn]
  h_fact_neg := by
    intro u ζcur net θ hlt
    change (if θ.get fin0 ≤ net then (1 : R) else 0) = 0
    have : ¬ θ.get fin0 ≤ net := not_le.mpr hlt
    simp [this]
  h_pact_pos := by right; rfl
  h_pact_neg := by left; rfl
  m_order := by simp [ZeroOneVisibleHidden, ZeroOne, SymmetricBinary]

/-- Coerce to the fully visible `ZeroOne` network (same activations and weights). -/
def toZeroOneParams (part : VisibleHiddenPartition U) (p : BMParams R U part) :
    _root_.Params (ZeroOne R U) :=
  { w := p.w, σ := p.σ, θ := p.θ, hw := p.hw, hw' := p.hw', h_arrows := p.h_arrows }

/-- Coerce a visible/hidden state to the fully visible network. -/
def toZeroOneState (part : VisibleHiddenPartition U) (s : BMState R U part) :
    NeuralNetwork.State (ZeroOne R U) :=
  { act := s.act, hp := s.hp }

/-- Embed a fully visible state into the visible/hidden type. -/
def ofZeroOneState (part : VisibleHiddenPartition U) (s : NeuralNetwork.State (ZeroOne R U)) :
    BMState R U part :=
  { act := s.act, hp := s.hp }

/-- Coercion commutes with forcing a site to `ζ_pos`. -/
lemma toZeroOneState_updPos (part : VisibleHiddenPartition U) (s : BMState R U part) (u : U) :
    toZeroOneState part (updPos s u) = updPos (toZeroOneState part s) u := by
  ext v
  simp [toZeroOneState, updPos, Function.update, instTwoState, TwoStateNeuralNetwork.ζ_pos]

/-- Coercion commutes with forcing a site to `ζ_neg`. -/
lemma toZeroOneState_updNeg (part : VisibleHiddenPartition U) (s : BMState R U part) (u : U) :
    toZeroOneState part (updNeg s u) = updNeg (toZeroOneState part s) u := by
  ext v
  simp [toZeroOneState, updNeg, Function.update, instTwoState, TwoStateNeuralNetwork.ζ_neg]

/-- Active state value on visible/hidden `{0,1}` BM. -/
@[simp] lemma NN_ζ_pos (part : VisibleHiddenPartition U) :
    @TwoStateNeuralNetwork.ζ_pos R U R _ _ _ (NN R U part) (instTwoState part) = (1 : R) := rfl

/-- Inactive state value on visible/hidden `{0,1}` BM. -/
@[simp] lemma NN_ζ_neg (part : VisibleHiddenPartition U) :
    @TwoStateNeuralNetwork.ζ_neg R U R _ _ _ (NN R U part) (instTwoState part) = (0 : R) := rfl

/-- Same `{0,1}` scale gap as `ZeroOne` (`scale_zeroOne`). -/
lemma scale_zeroOneVisibleHidden (part : VisibleHiddenPartition U) (f : R →+* ℝ) :
    scale (R := R) (U := U) (ζ := R) (NN := NN R U part) (f := f) = f 1 := by
  unfold scale
  rw [NN_ζ_pos part, NN_ζ_neg part]
  simp [ZeroOneVisibleHidden, ZeroOne, SymmetricBinary, map_one, map_zero, sub_zero]

/-- Coercion preserves single-site outputs (`fout` is the identity on `{0,1}`). -/
lemma toZeroOneState_out (part : VisibleHiddenPartition U) (s : BMState R U part) (u : U) :
    NeuralNetwork.State.out (toZeroOneState part s) u = NeuralNetwork.State.out s u := by
  simp [NeuralNetwork.State.out, toZeroOneState, ZeroOneVisibleHidden, ZeroOne, SymmetricBinary]

/-- Local field (`State.net`) is unchanged under coercion to `ZeroOne`. -/
lemma toZeroOneState_net (part : VisibleHiddenPartition U) (p : BMParams R U part)
    (s : BMState R U part) (u : U) :
    NeuralNetwork.State.net (toZeroOneParams part p) (toZeroOneState part s) u =
      NeuralNetwork.State.net p s u := by
  simp only [NeuralNetwork.State.net, toZeroOneParams, toZeroOneState,
    ZeroOneVisibleHidden, ZeroOne, SymmetricBinary]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with hx
  · rfl
  · simp only [NeuralNetwork.State.out, toZeroOneState, ZeroOneVisibleHidden, ZeroOne, SymmetricBinary]

end BMVisible

#lint only docBlame
