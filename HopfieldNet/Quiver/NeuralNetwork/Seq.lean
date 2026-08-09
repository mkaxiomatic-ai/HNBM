/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import HopfieldNet.Quiver.NeuralNetwork.Main

namespace Sequential

/--
A `SequentialArch ζ` specifies the architecture of a sequential (feedforward) neural network :
a list of layer widths `layerWidths` — of successive layers; e.g. `[4, 16, 3]` means 4 input neurons,
16 hidden neurons, and 3 output neurons, and a corresponding list of activation `activations`
descriptors, one for each layer.
-/
structure SequentialArch (ζ : Type) where
  layerWidths : List ℕ
  activations  : List ζ
  -- layer and activation lists have the same length.
  h_len_eq     : layerWidths.length = activations.length
  -- there are at least two layers (input and output).
  h_min_layers : layerWidths.length ≥ 2
  -- every width is strictly positive.
  h_pos_widths : ∀ w ∈ layerWidths, w > 0

variable (R : Type) [Semiring R]

/--
  We identify a neuron in the graph by a pair: (Layer Idx, Neuron Idx).
  This maps the sequential structure to a set of vertices U.
-/
structure SeqNeuron (arch : SequentialArch ζ) where
  layerIdx : Fin arch.layerWidths.length
  neuronIdx : Fin (arch.layerWidths.get layerIdx)

instance (arch : SequentialArch ζ) : DecidableEq (SeqNeuron arch) :=
  fun a b => match a, b with
  | ⟨l1, n1⟩, ⟨l2, n2⟩ =>
    if h : l1 = l2 then
      if h2 : n1.val = n2.val then isTrue (by aesop)
      else isFalse (by intro eq; injection eq; aesop)
    else isFalse (by intro eq; injection eq; contradiction)

/--
  Adjacency definition for a Sequential Network (incoming edges):
  `Adj u v` means that `v` is in the immediate previous layer of `u`.
  This matches the forward-pass computation which sums over neurons `v` in the previous layer.
-/
def SeqAdj {arch : SequentialArch ζ} (u v : SeqNeuron arch) : Prop :=
  v.layerIdx.val + 1 = u.layerIdx.val

/--
  Converting the Sequential Architecture into a NeuralNetwork.
-/
def toNeuralNetwork (arch : SequentialArch ζ) (actMap : ζ → R → R) :
    NeuralNetwork R (SeqNeuron arch) R := {
  Hom u v := PLift (SeqAdj u v)
  Ui := { u | u.layerIdx.val = 0 }
  Uo := { u | u.layerIdx.val = arch.layerWidths.length - 1 }
  Uh := { u | u.layerIdx.val > 0 ∧ u.layerIdx.val < arch.layerWidths.length - 1 }
  hUi := by
    have h0width : 0 < arch.layerWidths.get ⟨0, by grind [arch.h_min_layers]⟩ := by
      simpa using (arch.h_pos_widths
       (arch.layerWidths.get ⟨0, by grind [arch.h_min_layers]⟩) (by simp))
    refine Set.nonempty_iff_ne_empty'.mp
      ⟨⟨⟨0, by grind [arch.h_min_layers]⟩, ⟨0, h0width⟩⟩, rfl⟩
  hUo := by
    refine Set.nonempty_iff_ne_empty'.mp ?_
    have hlast : arch.layerWidths.length - 1 < arch.layerWidths.length := by
      cases h : arch.layerWidths.length with
      | zero =>
        have : ¬ (2 ≤ 0) := by decide
        exact (this (by simpa [h] using arch.h_min_layers)).elim
      | succ n => simp
    refine ⟨⟨⟨arch.layerWidths.length - 1, hlast⟩, ⟨0, ?_⟩⟩, rfl⟩
    · simpa using (arch.h_pos_widths (arch.layerWidths.get
        ⟨arch.layerWidths.length - 1, hlast⟩) (by simp))
  hU := by ext x; simp; grind
  hhio := by ext x; simp; grind
  κ1 := fun u => 1
  κ2 := fun _ => 0
  fnet := fun u w_row actMap params =>
    if h : u.layerIdx.val = 0 then 0 else
      let dot_prod := Finset.sum (Finset.univ : Finset
       (Fin (arch.layerWidths.get ⟨u.layerIdx.val - 1, by grind⟩))) (fun i =>
        let v : SeqNeuron arch := ⟨⟨u.layerIdx.val - 1, by grind⟩, i⟩
        (w_row v) * (actMap v))
      dot_prod + (params.get ⟨0, by simp⟩)
  fout := fun _ x => x
  fact := fun u x _ _ =>
    if u.layerIdx.val = 0 then x else
      actMap (arch.activations.get (u.layerIdx.cast arch.h_len_eq)) x
  pact := fun _ => True
  pw := fun _ _ _ => True
  hpact := fun _ _ _ _ _ _ _ _ _ => trivial
  pm _ := True
  m := fun _ => 0
}

variable {R : Type} [Semiring R] (ζ : Type) (actMap : ζ → R → R)
  (arch : SequentialArch ζ)

open NeuralNetwork

/-- The specific Neural Network instance derived from a Sequential Architecture. -/
abbrev SeqNet : NeuralNetwork R (SeqNeuron arch) R :=
  toNeuralNetwork (R := R) arch actMap

/-- A State for a sequential network is just a mapping from (Layer, Index) to a value. -/
abbrev SeqState := NeuralNetwork.State (SeqNet (R:=R) ζ actMap arch)

/-- Parameters for a sequential network. -/
abbrev SeqParams := Params (SeqNet (R:=R) ζ actMap arch)

lemma pred_layer_lt (h : (SeqNet (R := R) ζ actMap arch).Hom u v) :
  v.layerIdx < u.layerIdx := by
  refine Fin.lt_def.2 ?_
  have hv : v.layerIdx.val + 1 = u.layerIdx.val := by
    simpa [SeqAdj] using h.down
  grind

/-- Input neurons are stable. -/
lemma input_is_stable (s : SeqState (R := R) ζ actMap arch)
    (u : SeqNeuron arch) (hu : u.layerIdx.val = 0) : (s.Up params u).act u = s.act u := by
  simp [State.Up, SeqNet, toNeuralNetwork, hu]

/--
  A Sequential Network implies a specific order: Layer 1, then Layer 2, etc.
  We define a function that generates this specific list of neurons and
  iterate from layer 1 (first hidden) to the last layer.
  Layer 0 (Input) is usually fixed by the external input and not
  "updated" by the network function.
-/
def sequentialOrder : List (SeqNeuron arch) :=
  let updateLayers : List (Fin arch.layerWidths.length) :=
    (List.finRange arch.layerWidths.length).drop 1 -- Skip layer 0

  updateLayers.flatMap (fun layerId => by
    let w := arch.layerWidths.get layerId
    let neurons : List (Fin w) := List.finRange (arch.layerWidths.get layerId)
    apply neurons.map
    intros neuronId
    exact { layerIdx := layerId, neuronIdx := neuronId })

/-- Generates list of neurons: Layer 1, then Layer 2, etc. -/
def sequentialOrder' (arch : SequentialArch ζ) : List (SeqNeuron arch) :=
  ((List.finRange arch.layerWidths.length).drop 1).flatMap (fun l =>
    (List.finRange (arch.layerWidths.get l)).map (fun n => ⟨l, n⟩)
  )

variable (arch : SequentialArch ζ) (params : SeqParams (R:=R) ζ actMap arch)
         (inputState : SeqState (R:=R) ζ actMap arch)

/--
This is the forward pass. We take an initial state and run the updates in the specific `sequentialOrder`.
-/
def forwardPass (inputState : SeqState (R:=R) ζ actMap arch) (h_init : inputState.onlyUi) :
  SeqState (R := R ) ζ actMap arch :=
  State.workPhase params inputState h_init (sequentialOrder ζ arch)

inductive CustomActivations
  | ReLU
  | Softplus
  | Identity

def Interpreter (R : Type) [LinearOrder R] [Zero R] :
    CustomActivations → R → R
  | .ReLU, x => max 0 x
  | .Softplus, x => x
  | .Identity, x => x

def exArch : SequentialArch CustomActivations := {
  layerWidths := [2, 2, 1]
  activations  := [.Identity, .ReLU, .Softplus]
  h_len_eq     := rfl
  h_min_layers := by decide
  h_pos_widths := by decide}

def exParams : SeqParams (R := ℚ) (ζ := CustomActivations)
    (actMap := Interpreter ℚ) exArch := {
  σ := fun u => Vector.replicate 1 (0 : ℚ)
  θ := fun _ => Vector.replicate 0 (0 : ℚ)
  w := fun u v =>
    if hv : v.layerIdx.val + 1 = u.layerIdx.val then
      match u.layerIdx.val, u.neuronIdx.val, v.layerIdx.val, v.neuronIdx.val with
      | 1, 0, 0, 0 =>  1
      | 1, 0, 0, 1 => -1
      | 1, 1, 0, 0 => -1
      | 1, 1, 0, 1 =>  1
      | 2, 0, 1, 0 => 1
      | 2, 0, 1, 1 => 1
      | _, _, _, _ => 0
    else 0
  hw := by
    intro u v h1
    have h' : ¬ (v.layerIdx.val + 1 = u.layerIdx.val) := by
      intro hv
      apply h1
      simpa [SeqNet, toNeuralNetwork, SeqAdj] using (hv)
    simp [h']
  hw' := trivial
  h_arrows _ _ _ := trivial}

def exInputState : SeqState (R := ℚ) (ζ := CustomActivations)
    (actMap := Interpreter ℚ) exArch := {
  act := fun u =>
    match u.layerIdx.val, u.neuronIdx.val with
    | 0, 0 => 10
    | 0, 1 => 15
    | _, _ => 0
  hp := fun _ => trivial}

lemma exOnlyUi : exInputState.onlyUi := by
  constructor
  intro u hu
  simp [toNeuralNetwork] at hu
  cases u with
  | mk l n =>
    have hl : l.val ≠ 0 := by simpa using hu
    cases h : l.val with
    | zero => grind
    | succ k => simp [exInputState, h]; aesop

def showState (s : SeqState (R := ℚ) (ζ := CustomActivations)
      (actMap := Interpreter ℚ) exArch) : String :=
  let layers := List.finRange exArch.layerWidths.length
  String.intercalate "\n" (layers.map (fun l =>
    let width := exArch.layerWidths.get l
    let neurons := List.finRange width
    let acts := neurons.map (fun n => toString (s.act ⟨l, n⟩))
    s!"Layer {l}: {acts}" ))

def finalState : SeqState (R := ℚ) (ζ := CustomActivations)
    (actMap := Interpreter ℚ) exArch :=
  forwardPass (R := ℚ) (ζ := CustomActivations) (actMap := Interpreter ℚ)
    exArch exParams exInputState exOnlyUi

#eval showState finalState

end Sequential
