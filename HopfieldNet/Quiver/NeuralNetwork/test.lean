/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.Quiver.NeuralNetwork.Main

open Mathlib Finset BigOperators

/-- We keep the Matrix as the source of truth for both weights and topology. -/
def test.M : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of ![![0,0,4], ![1,0,0], ![-2,3,0]]

/-- We construct the NeuralNetwork instance. Note that we define 'Hom' here
  to satisfy the Quiver extension. -/
def test : NeuralNetwork ℚ (Fin 3) ℤ := {
  -- We define an arrow existing only if the matrix value is non-zero.
  Hom := fun u v => PLift (test.M u v ≠ 0)

  -- B. Architecture (Sets)
  Ui := {0,1}
  Uo := {2}
  Uh := ∅

  -- C. Proofs of Architecture (Same as original)
  hUi := Ne.symm (Set.ne_insert_of_notMem {1} fun a ↦ a)
  hUo := Set.singleton_ne_empty 2
  hU := by
     ext x
     simp only [Set.mem_univ, Fin.isValue, Set.union_singleton,
       Set.union_empty, Set.mem_insert_iff,
       Set.mem_singleton_iff, true_iff]
     revert x
     decide
  hhio := by
    simp only [Fin.isValue, Set.union_singleton, Set.empty_inter]
  κ1 := fun _ => 0
  κ2 := fun _ => 1
  fnet u w pred σ := ∑ v, w v * pred v
  fact u _ input θ := if input ≥ θ.get 0 then 1 else 0
  fout := fun u act => act
  pact := fun _ => True
  pw := fun _ _ _ => True -- We accept any arrow defined by our Hom
  hpact w _ _ _ σ θ _ pact u := pact u
  pwMat := by {
    intro u v
    exact (test.M u v ≠ 0)
  }
  pm W := True
  m := fun _ => 0
}

def wθ : Params test where
  h_arrows := fun _ _ _ => True.intro
  w := test.M
  θ u := ⟨#[1], by
    simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add]
    unfold test
    simp only⟩
  σ := fun _ => Vector.emptyWithCapacity 0
  hw := fun u v h_no_arrow => by
    unfold test at h_no_arrow
    simp only [ne_eq, Decidable.not_not] at h_no_arrow
    exact h_no_arrow
  hw' := by simp only [test]

-- Helper for printing
instance : Repr (NeuralNetwork.State test) where
  reprPrec state _ :=
   ("acts: " ++ repr (state.act)) ++ ", outs: " ++
        repr (state.out) ++ ", nets: " ++ repr (state.net wθ)

-- Initial State
def test.extu : test.State := {
  act := ![1,0,0],
  hp := fun _ => trivial
}

lemma zero_if_not_mem_Ui : ∀ u : Fin 3,
  ¬ u ∈ ({0,1} : Finset (Fin 3)) → test.extu.act u = 0 := by decide

-- Proof that initial state respects input neuron constraints
lemma test.onlyUi : test.extu.onlyUi := by {
  constructor
  intros u hu
  apply zero_if_not_mem_Ui u
  simp only [Fin.isValue, mem_insert, mem_singleton, not_or]
  exact not_or.mp hu
}

-- Show the state after *each* asynchronous neuron update (not only the final state).

def test.seq : List (Fin 3) := [2,0,1,2,0,1,2]

/-- States after running `workPhase` on every prefix of `test.seq`.
Includes the initial state as the first element (empty prefix). -/
def test.workPhaseTrace : List test.State :=
  (test.seq.inits).map (fun pref =>
    NeuralNetwork.State.workPhase wθ test.extu test.onlyUi pref
  )

-- All intermediate states (including the initial one at the start)
--#eval test.workPhaseTrace

/-- Same trace, but labeled by the neuron updated at each step. -/
def test.workPhaseTraceLabeled : List ((Fin 3) × test.State) :=
  List.zip test.seq (test.workPhaseTrace.drop 1)

-- Each step: (neuron updated, resulting state)
#eval test.workPhaseTraceLabeled

-- The workphase for the asynchronous update of the sequence of neurons u3 , u2 , u1 , u3 , u2 , u1 , u3 ,

def test.seq' : List (Fin 3) := [2,1,0,2,1,0,2]

/-- States after running `workPhase` on every prefix of `test.seq'`.
Includes the initial state as the first element (empty prefix). -/
def test.workPhaseTrace' : List test.State :=
  (test.seq'.inits).map (fun pref =>
    NeuralNetwork.State.workPhase wθ test.extu test.onlyUi pref
  )

--#eval test.workPhaseTrace'

/-- Same trace, but labeled by the neuron updated at each step. -/
def test.workPhaseTraceLabeled' : List ((Fin 3) × test.State) :=
  List.zip test.seq' (test.workPhaseTrace'.drop 1)

#eval test.workPhaseTraceLabeled'

-- Final state (same as last element of the trace)
--#eval NeuralNetwork.State.workPhase wθ test.extu test.onlyUi test.seq'

-- /- Workphase: u3, u1, u2, u3, u1, u2, u3 -/
-- #eval NeuralNetwork.State.workPhase wθ test.extu test.onlyUi [2,0,1,2,0,1,2]

-- /- Workphase: u3, u2, u1, u3, u2, u1, u3 -/
-- #eval NeuralNetwork.State.workPhase wθ test.extu test.onlyUi [2,1,0,2,1,0,2]
