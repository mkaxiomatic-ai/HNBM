/-
Copyright (c) 2025 HNBM contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.Quiver.NeuralNetwork.Main

/-!
# Visible / hidden partition for Boltzmann machines

A **visible/hidden partition** splits the neuron set into units that carry data
(`U_vis`) and latent units (`U_hid = univ \ U_vis`).
-/

namespace BMVisible

/-- Visible/hidden split of the neuron set (stored as finsets for decidability). -/
structure VisibleHiddenPartition (U : Type) [Fintype U] [DecidableEq U] where
  /-- Visible neurons (patterns are presented here). -/
  visible : Finset U
  /-- At least one visible neuron. -/
  hvisible_nonempty : visible.Nonempty
  /-- At least one hidden neuron. -/
  hhidden_nonempty : (Finset.univ \ visible).Nonempty

variable {U : Type} [Fintype U] [DecidableEq U]

/-- Hidden neurons as a finset (for sweep orders). -/
def hiddenFinset (part : VisibleHiddenPartition U) : Finset U :=
  Finset.univ \ part.visible

/-- Visible neurons as a set (for `NeuralNetwork.Ui` / `Uo`). -/
def visSet (part : VisibleHiddenPartition U) : Set U :=
  (part.visible : Set U)

/-- Hidden neurons as a set. -/
def hidSet (part : VisibleHiddenPartition U) : Set U :=
  (hiddenFinset part : Set U)

/-- Membership in `visSet` is membership in the visible finset. -/
lemma mem_visSet_iff (part : VisibleHiddenPartition U) {u : U} :
    u ∈ visSet part ↔ u ∈ part.visible := by
  simp [visSet]

/-- Membership in `hidSet` is membership in `hiddenFinset`. -/
lemma mem_hidSet_iff (part : VisibleHiddenPartition U) {u : U} :
    u ∈ hidSet part ↔ u ∈ hiddenFinset part := by
  simp [hidSet]

/-- Hidden units are exactly the non-visible ones. -/
lemma mem_hidSet_iff_not_vis (part : VisibleHiddenPartition U) {u : U} :
    u ∈ hidSet part ↔ u ∉ part.visible := by
  simp [hidSet, hiddenFinset, Finset.mem_sdiff, Finset.mem_univ, mem_visSet_iff]

/-- Visible and hidden sets are disjoint. -/
lemma disjoint_vis_hid (part : VisibleHiddenPartition U) :
    Disjoint (visSet part) (hidSet part) := by
  rw [Set.disjoint_iff]
  intro u ⟨hvis, hhid⟩
  exact (mem_hidSet_iff_not_vis part).mp hhid ((mem_visSet_iff part).mp hvis)

/-- Every neuron is visible or hidden. -/
lemma union_vis_hid (part : VisibleHiddenPartition U) :
    visSet part ∪ hidSet part = Set.univ := by
  ext u
  constructor
  · intro _; exact Set.mem_univ u
  · intro _
    by_cases hu : u ∈ part.visible
    · exact Or.inl ((mem_visSet_iff part).mpr hu)
    · exact Or.inr ((mem_hidSet_iff_not_vis part).mpr hu)

/-- Visible units are not hidden. -/
lemma not_mem_hidSet (part : VisibleHiddenPartition U) {u : U} (hu : u ∈ visSet part) :
    u ∉ hidSet part := by
  intro hhid
  exact ((mem_hidSet_iff_not_vis part).mp hhid) ((mem_visSet_iff part).mp hu)

/-- Hidden units are not visible. -/
lemma not_mem_visSet (part : VisibleHiddenPartition U) {u : U} (hu : u ∈ hidSet part) :
    u ∉ visSet part := by
  exact (mem_visSet_iff part).not.mpr ((mem_hidSet_iff_not_vis part).mp hu)

/-- `hiddenFinset` and `hidSet` have the same members. -/
lemma mem_hiddenFinset (part : VisibleHiddenPartition U) {u : U} :
    u ∈ hiddenFinset part ↔ u ∈ hidSet part :=
  (mem_hidSet_iff part).symm

/-- Default update order: all hidden neurons. -/
noncomputable def hiddenList (part : VisibleHiddenPartition U) : List U :=
  (hiddenFinset part).toList

end BMVisible

#lint only docBlame
