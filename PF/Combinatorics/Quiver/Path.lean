import PF.Data.List
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Combinatorics.Quiver.Path.Weight


open List

/-!
# Quiver.Path

This module provides definitions, theorems, and lemmas for manipulating and
reasoning about paths in a `Quiver` (directed graph). The key concepts and results include:

## 1. Weights on Paths
  - **Definitions:** `weight`, `weightFromVertices` assign values in a monoid/semiring to edges
  and extend multiplicatively to paths.
  - **Lemmas:** `weight_comp`, `weightFromVertices_comp` (multiplicativity under composition);
    `weight_pos`, `weightFromVertices_pos`, `weightFromVertices_nonneg` (positivity/non-negativity results).

## 2. Path Decomposition and Splitting
  - **Theorems/Lemmas:**
    - `path_decomposition_first_edge`, `path_decomposition_last_edge`: decompose a path at the first or last edge.
    - `exists_decomp_at_length`: split a path so the first component has a specified length.
    - `exists_decomp_of_mem_vertices`, `exists_decomp_of_mem_vertices_prop`: split at an arbitrary visited vertex, with a proposition version.
    - `split_at_vertex`: decompose a path precisely at the position of a chosen vertex.

## 3. Boundary and Crossing Edges
  - **Theorems:**
    - `exists_boundary_edge`, `exists_crossing_edge`: existence of boundary/crossing arrows for paths entering a set.

## 4. Vertices of a Path
  - **Definitions:** `«end»`, `activeVertices`, `vertices`, `activeFinset`.
  - **Lemmas:**
    - `vertices_length`, `vertices_head?`, `vertices_nonempty`, `vertices_comp`, `start_mem_vertices`.
    - Extraction lemmas for head/last and vertex membership.

## 5. Path Properties and Simplicity
  - **Definitions:**
    - `isStrictlySimple`: predicate for strictly simple (no repeated vertices except possibly endpoints) paths.
  - **Theorems/Lemmas:**
    - `isStrictlySimple_of_shortest`: shortest path between two vertices is strictly simple.
    - Related characterizations and implications for path minimality and structure.

## 6. Induced Subquivers and Embeddings
  - **Definitions:** `Quiver.inducedQuiver`, `Subquiver.embedding`.
  - **Lemma:** `mapPath_embedding_vertices_in_set` (embedded paths remain in the subset).

## 7. Prefunctor Interaction
  - **Lemma:** `Prefunctor.end_map` (compatibility of path endpoint with functorial mapping).

## 8. Path Replication
  - **Definitions:** `replicate`.
  - **Lemma:** `length_replicate` (length scales with replication).
-/

namespace Quiver.Path

variable {V : Type*} [Quiver V] {R : Type*}

section Weight

variable [Monoid R]

def weightFromVertices (w : V → V → R) : ∀ {i j : V}, Path i j → R :=
  weight (fun {i j} (_ : i ⟶ j) => w i j)

lemma weightFromVertices_comp (w : V → V → R) {a b c : V} (p : Path a b) (q : Path b c) :
    weightFromVertices w (p.comp q) = weightFromVertices w p * weightFromVertices w q := by
  simp only [weightFromVertices, weight_comp]

end Weight

section RealWeight

variable {w : V → V → ℝ} {i j : V} (p : Path i j)

lemma weightFromVertices_pos (hw : ∀ i j : V, 0 < w i j) : 0 < weightFromVertices w p := by
  apply weight_pos; intro i j _; exact hw i j

lemma weightFromVertices_nonneg (hw : ∀ i j : V, 0 ≤ w i j) : 0 ≤ weightFromVertices w p := by
  induction p using Path.rec with
  | nil => simp only [weightFromVertices, weight, zero_le_one]
  | cons p' e ih => simp only [weightFromVertices, weight]; exact mul_nonneg ih (hw _ _)

end RealWeight

section PathDecomposition

variable {V : Type*} [Quiver V] {a b : V} (p : Path a b)

/-- Every non-empty path can be decomposed as an initial path plus a final edge. -/
lemma path_decomposition_last_edge {a b : V} (p : Path a b) (h : p.length > 0) :
    ∃ (c : V) (p' : Path a c) (e : c ⟶ b), p = p'.cons e := by
  cases p with | nil => simp at h | cons p' e => exact ⟨_, p', e, rfl⟩

/-- Every non-empty path can be decomposed as a first edge plus a remaining path. -/
lemma path_decomposition_first_edge (h : p.length > 0) :
    ∃ (c : V) (e : a ⟶ c) (p' : Path c b), p = e.toPath.comp p' ∧ p.length = p'.length + 1 := by
  have h_len : p.length = (p.length - 1) + 1 := by omega
  obtain ⟨c, e, p', hp', rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p h_len
  use c, e, p'; exact ⟨rfl, by omega⟩

end PathDecomposition

section BoundaryEdges

variable {V : Type*} [Quiver V]

lemma cons_eq_comp_toPath {a b c : V} (p : Path a b) (e : b ⟶ c) : p.cons e = p.comp e.toPath :=  rfl

/-- A path from a vertex not in `S` to a vertex in `S` must cross the boundary. -/
theorem exists_boundary_edge {a b : V} (p : Path a b) (S : Set V)
    (ha_not_in_S : a ∉ S) (hb_in_S : b ∈ S) :
    ∃ (u v : V) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      u ∉ S ∧ v ∈ S ∧ p = p₁.comp (e.toPath.comp p₂) := by
  induction' h_len : p.length with n ih generalizing b
  · obtain rfl := eq_of_length_zero p h_len
    exact (ha_not_in_S hb_in_S).elim
  · obtain ⟨c, p', e, rfl⟩ := path_decomposition_last_edge p (h_len.symm ▸ Nat.zero_lt_succ _)
    by_cases hc : c ∈ S
    · obtain ⟨u, v, e_uv, p₁, p₂, hu, hv, rfl⟩ := ih p' hc (Nat.succ_inj.mp h_len)
      exact ⟨u, v, e_uv, p₁, p₂.cons e, hu, hv, rfl⟩
    · exact ⟨c, b, e, p', Path.nil, hc, hb_in_S, rfl⟩

/-- A path from a vertex in `S` to a vertex not in `S` must cross the boundary. -/
theorem exists_boundary_edge_from_set {a b : V} (p : Path a b) (S : Set V)
    (ha_in_S : a ∈ S) (hb_not_in_S : b ∉ S) :
    ∃ (u v : V) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      u ∈ S ∧ v ∉ S ∧ p = p₁.comp (e.toPath.comp p₂) := by
  obtain ⟨u, v, e, p₁, p₂, hu_not_in_compl, hv_in_compl, hp⟩ :=
    exists_boundary_edge p Sᶜ (by grind) (by grind)
  grind

/-- Alternative formulation: there exists an edge crossing the boundary. -/
theorem exists_crossing_edge {a b : V} (p : Path a b) (S : Set V)
    (ha_not_in_S : a ∉ S) (hb_in_S : b ∈ S) :
    ∃ (u v : V) (_ : u ⟶ v), u ∉ S ∧ v ∈ S := by
  obtain ⟨u, v, e, _, _, hu_not_S, hv_S, _⟩ := exists_boundary_edge p S ha_not_in_S hb_in_S
  exact ⟨u, v, e, hu_not_S, hv_S⟩

end BoundaryEdges

end Quiver.Path

namespace Quiver.Path

variable {V : Type*} [Quiver V]

/-- The set of vertices in a path. -/
def activeVertices {a : V} : ∀ {b : V}, Path a b → Set V
  | _, nil => {a}
  | _, cons p e => activeVertices p ∪ {«end» (cons p e)}

@[simp] lemma activeVertices_nil {a : V} : activeVertices (nil : Path a a) = {a} := rfl
@[simp] lemma activeVertices_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
  activeVertices (p.cons e) = activeVertices p ∪ {c} := by simp [activeVertices]

-- Vertices of a path are always non-empty
lemma vertices_nonempty' {V : Type*} [Quiver V] {a b : V} (p : Path a b) : p.vertices.length > 0 := by
  induction p with
  | nil => simp only [vertices_nil, List.length_cons, List.length_nil, le_refl, Nat.eq_of_le_zero,
    zero_add, gt_iff_lt, Nat.lt_one_iff, pos_of_gt]
  | cons p' e ih =>
    rw [vertices_cons]
    simp only [List.concat_eq_append, List.length_append, List.length_cons, List.length_nil,
      zero_add, gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, ih, Nat.lt_one_iff, pos_of_gt, or_self]

/-- The set of vertices in a path, excluding the final vertex. -/
def activeFinset [DecidableEq V] {a b : V} (p : Path a b) : Finset V :=
  p.vertices.dropLast.toFinset

def activeVertices' {a : V} {b : V} (p : Path a b) : Set V :=
  {v | v ∈ p.vertices}

@[simp]
lemma mem_activeVertices {a b : V} (p : Path a b) (v : V) :
    v ∈ p.activeVertices' ↔ v ∈ p.vertices := by
  rfl

/-- The finset of vertices in a path. -/
def vertexFinset [DecidableEq V] {a b : V} (p : Path a b) : Finset V :=
  p.vertices.toFinset

/--
A vertex `x` is in the `activeFinset` of a path `p` if and only if it is in the `dropLast` of the `vertices` list of `p`.
-/
@[simp]
lemma mem_activeFinset_iff [DecidableEq V] {a b : V} (p : Path a b) {x : V} :
    x ∈ activeFinset p ↔ x ∈ p.vertices.dropLast := by
  simp only [activeFinset, List.mem_toFinset]

lemma vertices_nonempty {a : V} {b : V} (p : Path a b) : p.vertices ≠ [] := by
  rw [← List.length_pos_iff_ne_nil, vertices_length]; omega

variable {α : Type*} [DecidableEq α]

/-- A path from a single arrow. -/
def List.toPath {a b : V} (e : a ⟶ b) : Path a b :=
  Path.nil.cons e

/-- Given vertices lists from a path composition, the prefix path's vertices is a prefix of the full path's vertices -/
lemma isPrefix_dropLast_of_comp_eq {V : Type*} [Quiver V] {a b c : V} {p : Path a b} {p₁ : Path a c} {p₂ : Path c b}
    (h : p.vertices = p₁.vertices.dropLast ++ p₂.vertices) : p₁.vertices.dropLast.IsPrefix p.vertices := by
  rw [h]
  exact List.prefix_append p₁.vertices.dropLast p₂.vertices

/-- The head of the vertices list is the start vertex. -/
@[simp]
lemma vertices_head_eq_start {a b : V} (p : Path a b) : p.vertices.head (vertices_nonempty p) = a := by
  induction p with
  | nil => simp only [vertices_nil, List.head_cons]
  | cons p' _ ih =>
    simp only [vertices_cons, List.concat_eq_append]
    have : p'.vertices ≠ [] := vertices_nonempty p'
    simp only [List.head_append_of_ne_nil this]
    exact ih

/-- The last element of the vertices list is the end vertex. -/
@[simp]
lemma vertices_getLast_eq_end {a b : V} (p : Path a b) :
  p.vertices.getLast (vertices_nonempty p) = b := by
  exact vertices_getLast p (vertices_nonempty p)

variable {V : Type*} [Quiver V]

lemma end_prefix_eq_get_vertices {a b c : V} (p₁ : Path a c) (p₂ : Path c b) :
    c = (p₁.comp p₂).vertices.get
        ⟨p₁.length, by
  simp only [vertices_comp, List.length_append, List.length_dropLast,
    vertices_length, add_tsub_cancel_right, lt_add_iff_pos_right, add_pos_iff,
    Nat.lt_one_iff, pos_of_gt, or_true]⟩ := by
  simp only [List.get_eq_getElem, vertices_comp, List.length_dropLast, vertices_length,
    add_tsub_cancel_right, le_refl, List.getElem_append_right, tsub_self, List.getElem_zero,
    vertices_head_eq_start]


lemma mem_vertices_to_active {V : Type*} [Quiver V]
    {a b : V} {p : Path a b} {x : V} :
    x ∈ p.vertices → x ∈ p.activeVertices := by
  intro hx
  induction p with
  | nil =>
      aesop
  | cons p' e ih =>
      -- For (p'.cons e), vertices = p'.vertices.concat c and activeVertices = activeVertices p' ∪ {c}.
      simp [vertices_cons] at hx
      cases hx with
      | inl hx_in =>
          have hx_act : x ∈ p'.activeVertices := ih hx_in
          simp [activeVertices_cons, hx_act]
      | inr hx_eq =>
          subst hx_eq
          simp [activeVertices_cons]

end Quiver.Path

namespace Prefunctor

open Quiver

variable {V W : Type*} [Quiver V] [Quiver W] (F : V ⥤q W)

@[simp]
lemma end_map {a b : V} (p : Path a b) : F.obj (p.end) = (F.mapPath p).end := by
  induction p with
  | nil => rfl
  | cons p' e ih => simp

end Prefunctor

open Quiver

namespace Quiver

/-- The quiver structure on a subtype is induced by the quiver structure on the original type.
    An arrow from `a : S` to `b : S` exists if an arrow from `a.val` to `b.val` exists. -/
def inducedQuiver {V : Type*} [Quiver V] (S : Set V) : Quiver S :=
  ⟨fun a b => a.val ⟶ b.val⟩

end Quiver
namespace Quiver.Subquiver

variable {V : Type*} [Quiver V] (S : Set V)

attribute [local instance] inducedQuiver

/-- The embedding of an induced subquiver on a set `S` into the original quiver. -/
@[simps]
def embedding : Prefunctor S V where
  obj := Subtype.val
  map := id

/-- The vertices in a path mapped by the embedding are all in the original set S. -/
@[simp]
lemma mapPath_embedding_vertices_in_set {i j : S} (p : Path i j) :
  ∀ v, v ∈ ((embedding S).mapPath p).activeVertices → v ∈ S := by
  induction p with
  | nil =>
    intro v hv
    simp only [Prefunctor.mapPath_nil, Path.activeVertices_nil, Set.mem_singleton_iff] at hv
    subst hv
    exact i.property
  | cons p' e ih =>
    intro v hv
    simp only [Prefunctor.mapPath_cons, Path.activeVertices_cons, Set.mem_union,
               Set.mem_singleton_iff] at hv
    cases hv with
    | inl h => exact ih v h
    | inr h => subst h; simp_all only [embedding_obj, Subtype.coe_prop]

open Quiver.Path

/--
If a path in the original quiver only visits vertices in a set `S`, it can be lifted
to a path in the induced subquiver on `S`.
-/
def lift_path_to_induced {S : Set V} [DecidablePred (· ∈ S)]
    {i j : V} (p : Path i j) (hp : ∀ k, k ∈ p.vertices → k ∈ S) :
    letI : Quiver S := inducedQuiver S
    Path (⟨i, hp i (start_mem_vertices p)⟩ : S) (⟨j, hp j (end_mem_vertices p)⟩ : S) := by
  letI : Quiver S := inducedQuiver S
  induction p with
  | nil => exact Path.nil
  | cons p' e ih =>
    exact Path.cons (ih (fun k hk => hp k ((mem_vertices_cons p' e).mpr (Or.inl hk)))) e

end Quiver.Subquiver

namespace Quiver.Path
open Quiver
variable {V : Type*} [Quiver V]

/--
Construct a path by repeating a loop `n` times.
`replicate n p` is the path `p.comp(p.comp(...p))` where `p` is composed `n` times.
If `n=0`, it is the nil path.
-/
def replicate (n : ℕ) {a : V} (p : Path a a) : Path a a :=
  match n with
  | 0 => Path.nil
  | k + 1 => (replicate k p).comp p

@[simp]
lemma length_replicate (n : ℕ) {a : V} (p : Path a a) :
  (replicate n p).length = n * p.length := by
  induction n with
  | zero => simp only [replicate, length_nil, zero_mul]
  | succ k ih =>
    simp only [replicate, length_comp, ih, add_comm, Nat.succ_mul]

variable {V : Type*} [Quiver V]



variable {V : Type*} [Quiver V]

/-!  ### Path splitting utilities -/

open List

/-- Given a path `p : Path a b` and an index `n ≤ p.length`,
    we can split `p = p₁.comp p₂` with `p₁.length = n`. -/
theorem exists_decomp_at_length {a b : V} (p : Path a b) {n : ℕ} (hn : n ≤ p.length) :
    ∃ (c : V) (p₁ : Path a c) (p₂ : Path c b), p = p₁.comp p₂ ∧ p₁.length = n := by
  induction p generalizing n with
  | nil =>
    obtain rfl : n = 0 := Nat.eq_zero_of_le_zero hn
    exact ⟨_, .nil, .nil, rfl, rfl⟩
  | cons p e ih =>
    rcases hn.lt_or_eq with h | rfl
    · obtain ⟨c, p₁, p₂, rfl, rfl⟩ := ih (Nat.le_of_lt_succ h)
      exact ⟨c, p₁, p₂.cons e, rfl, rfl⟩
    · exact ⟨_, p.cons e, .nil, rfl, rfl⟩

theorem exists_decomp_of_mem_vertices {a b v : V} (p : Path a b)
  (h : v ∈ p.vertices) : ∃ (p₁ : Path a v) (p₂ : Path v b), p = p₁.comp p₂ := by
  obtain ⟨l₁, l₂, hv⟩ := List.exists_mem_split h
  have h_len : l₁.length ≤ p.length := by
    have : p.vertices.length = p.length + 1 := vertices_length p
    have : l₁.length < p.vertices.length := by
      rw [hv, List.length_append, List.length_cons]
      omega
    omega
  obtain ⟨c, p₁, p₂, hp, hl⟩ := exists_decomp_at_length p h_len
  suffices hvc : v = c by
    subst hvc
    exact ⟨p₁, p₂, hp⟩
  have h_verts : p.vertices = p₁.vertices.dropLast ++ p₂.vertices := by
    rw [hp, vertices_comp]
  have h_l1_len : l₁.length = p₁.vertices.dropLast.length := by
    have : p₁.vertices.length = p₁.length + 1 := vertices_length p₁
    simp only [List.length_dropLast, this, hl, add_tsub_cancel_right]
  have h_l1_eq : l₁ = p₁.vertices.dropLast := by
    have : l₁ ++ v :: l₂ = p₁.vertices.dropLast ++ p₂.vertices := by
      rw [← hv, h_verts]
    exact List.append_inj_left this h_l1_len
  have h_v_l2 : v :: l₂ = p₂.vertices := by
    have : l₁ ++ v :: l₂ = p₁.vertices.dropLast ++ p₂.vertices := by
      rw [← hv, h_verts]
    rw [h_l1_eq] at this
    exact List.append_cancel_left this
  have : p₂.vertices.head? = some c := by
    cases p₂ with
    | nil => simp only [vertices_nil, List.head?_cons]
    | cons _ _ => exact vertices_head? _
  rw [← h_v_l2] at this
  simp only [List.head?_cons, Option.some.injEq] at this
  exact this

/-
/- Equality of paths implies equality of their start and end vertices. -/
lemma eq_of_heq {a a' b b' : V} {p : Path a b} {p' : Path a' b'} (h : HEq p p') :
  a = a' ∧ b = b' := by
  -- derive equalities of start and end vertices using heterogeneous equality
  have h₁ : start p = start p' :=
    Eq.ndrec (motive := fun x => start p = x) rfl (congrArg start h)
  have h₂ : «end» p = «end» p' :=
    Eq.ndrec (motive := fun x => «end» p = x) rfl (congrArg «end» h)
  simp [Path.start, Path.end] at h₁ h₂
  exact ⟨h₁, h₂⟩

@[simp]
lemma start_eq_of_heq {a a' b b' : V} {p : Path a b} {p' : Path a' b'} (h : HEq p p') :
  a = a' :=
  (eq_of_heq h).1

@[simp]
lemma end_eq_of_heq {a a' b b' : V} {p : Path a b} {p' : Path a' b'} (h : HEq p p') :
  b = b' :=
  (eq_of_heq h).2-/


theorem split_at_vertex {a b : V} (p : Path a b) (i : ℕ) (hi : i < p.vertices.length) :
    ∃ (v : V) (p₁ : Path a v) (p₂ : Path v b), p = p₁.comp p₂ ∧ p₁.length = i ∧ v = p.vertices.get ⟨i, hi⟩ := by
  -- Convert vertex index bound to path length bound and decompose
  obtain ⟨v, p₁, p₂, rfl, rfl⟩ := exists_decomp_at_length p (Nat.lt_succ_iff.1 (by rwa [vertices_length] at hi))
  -- Close with the prefix-endpoint identity
  exact ⟨v, p₁, p₂, rfl, rfl, by simp⟩

end Quiver.Path

namespace Quiver.Path
open Quiver
variable {V : Type*} [Quiver V]

/-- A path is simple if it does not visit any vertex more than once, with the possible
exception of the final vertex, which may be the same as the start vertex in a cycle. -/
def IsSimple' {a b : V} (p : Path a b) : Prop :=
  p.vertices.dropLast.Nodup ∧
  (a = b → p.vertices.dropLast.length = p.length) ∧
  (a ≠ b → p.end ∉ p.vertices.dropLast)

lemma isSimple_nil {a : V} : IsSimple' (nil : Path a a) := by
  simp only [IsSimple', vertices_nil, dropLast_singleton, nodup_nil, List.length_nil, le_refl,
    Nat.eq_of_le_zero, length_nil, imp_self, ne_eq, not_true_eq_false, not_mem_nil,
    not_false_eq_true, implies_true, and_self]

/-- A path is simple if it does not contain any vertex more than once.
This is a strict definition; a cycle `a ⟶ ... ⟶ a` of non-zero length is not simple. -/
@[simp]
def IsStrictlySimple {a b : V} (p : Path a b) : Prop := p.vertices.Nodup

lemma isStrictlySimple_nil {a : V} : IsStrictlySimple (nil : Path a a) := by
  simp only [IsStrictlySimple, vertices_nil, nodup_cons, not_mem_nil, not_false_eq_true, nodup_nil,
    and_self]

@[simp]
lemma isStrictlySimple_cons [DecidableEq V] {a b c : V} (p : Path a b) (e : b ⟶ c) :
  IsStrictlySimple (p.cons e) ↔ IsStrictlySimple p ∧ c ∉ p.vertices := by
  simp only [IsStrictlySimple, vertices_cons]
  rw [List.nodup_concat]; aesop

/-- The set of vertices of a simple path has cardinality `p.length + 1`. -/
lemma card_vertexFinset_of_isStrictlySimple [DecidableEq V] {a b : V} {p : Path a b} (hp : IsStrictlySimple p) :
    p.vertexFinset.card = p.length + 1 := by
  simp [vertexFinset, List.toFinset_card_of_nodup hp, vertices_length]

lemma length_lt_card_of_isStrictlySimple [DecidableEq V] [Fintype V]
    {a b : V} {p : Path a b} (hp : IsStrictlySimple p) :
  p.length < Fintype.card V := by
  simpa [card_vertexFinset_of_isStrictlySimple hp, Nat.succ_eq_add_one] using
    (Finset.card_le_univ p.vertexFinset)

/-- If a path is not strictly simple, then there exists a vertex that occurs at least twice. -/
lemma not_strictly_simple_iff_exists_repeated_vertex [DecidableEq V] {a b : V} {p : Path a b} :
    ¬IsStrictlySimple p ↔ ∃ v, v ∈ p.vertices ∧ p.vertices.count v ≥ 2 := by
  rw [IsStrictlySimple, List.nodup_iff_not_contains_dup]
  push_neg
  simp only [List.ContainsDup]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, List.count_pos_iff.mp (by linarith), hv⟩
  · rintro ⟨v, _, hv⟩
    exact ⟨v, hv⟩


/-- Removing a positive-length cycle from a path gives a strictly shorter path with the same endpoints. -/
lemma remove_cycle_gives_shorter_path [DecidableEq V] {a v b : V}
    {p_prefix : Path a v} {p_cycle : Path v v} {p_rest : Path v b}
    (h_cycle_pos : p_cycle.length > 0) :
    (p_prefix.comp p_rest).length < (p_prefix.comp (p_cycle.comp p_rest)).length := by
  simp only [length_comp]
  simp_all only [gt_iff_lt, add_lt_add_iff_left, lt_add_iff_pos_left]

open List

/-- If a vertex c appears in path p, c must either be the end vertex or appear in the tail of vertices. -/
lemma vertex_in_path_cases {a b c : V} (p : Path a b) (h : c ∈ p.vertices) :
    c = b ∨ c ∈ p.vertices.dropLast := by
  have h_dec := List.dropLast_append_getLast (vertices_nonempty p)
  rw [← h_dec, List.mem_append, List.mem_singleton] at h
  aesop

/-- If we have a path p from a to b with c ∈ p.vertices,
    and c is not the end vertex b, then it appears in a proper prefix of the path. -/
lemma exists_prefix_with_vertex [DecidableEq V] {a b c : V} (p : Path a b) (h : c ∈ p.vertices) (h_ne : c ≠ b) :
    ∃ (p₁ : Path a c) (p₂ : Path c b), p = p₁.comp p₂ := by
  obtain ⟨v, p₁, p₂, h_comp, _, hc⟩ := split_at_vertex p _ (List.idxOf_lt_length_of_mem h)
  rcases hc.trans (List.get_idxOf_of_mem h) with rfl
  exact ⟨p₁, p₂, h_comp⟩

/-- Split a path at the **last** occurrence of a vertex. -/
theorem exists_decomp_of_mem_vertices_prop
    [DecidableEq V] {a b x : V} (p : Path a b) (hx : x ∈ p.vertices) :
    ∃ (p₁ : Path a x) (p₂ : Path x b),
      p = p₁.comp p₂ ∧ x ∉ p₂.vertices.tail := by
  induction p with
  | nil =>
    obtain rfl : x = a := by simpa [vertices_nil] using hx
    exact ⟨Path.nil, Path.nil, by simp, by simp [vertices_nil]⟩
  | cons p' e ih =>
    by_cases h_end : x = (p'.cons e).end
    · obtain rfl := h_end
      exact ⟨p'.cons e, Path.nil, by aesop, by simp [vertices_nil]⟩
    · rcases (mem_vertices_cons p' e).mp hx with h_in | rfl
      · obtain ⟨p₁, p₂, rfl, h_not_tail⟩ := ih h_in
        refine ⟨p₁, p₂.cons e, rfl, fun h_tail ↦ ?_⟩
        cases hv : p₂.vertices <;> simp_all [vertices_cons, List.mem_append, List.mem_concat]
      · exact (h_end rfl).elim

theorem isStrictlySimple_of_shortest [DecidableEq V]
    {a b : V} (p : Path a b)
    (h_min : ∀ q : Path a b, p.length ≤ q.length) :
    IsStrictlySimple p := by
  classical
  by_contra h_dup
  obtain ⟨v, hv_in, hv_ge₂⟩ := not_strictly_simple_iff_exists_repeated_vertex.mp h_dup
  obtain ⟨p₁, p₂, hp, hv_not_tail⟩ := exists_decomp_of_mem_vertices_prop p hv_in

  have h_head : p₂.vertices.head? = some v := by
    cases p₂ with
    | nil => rfl
    | cons p' e => simp [vertices_cons, List.concat_eq_append, vertices_head?]

  have h_p2_count : p₂.vertices.count v = 1 := by
    cases hv : p₂.vertices with
    | nil => exact (vertices_nonempty p₂ hv).elim
    | cons hd tl =>
      -- Safely rewrite hd to v without deleting v from the context!
      have h_eq : hd = v := Option.some_inj.mp (by simpa [hv] using h_head)
      rw [h_eq] at hv ⊢
      have h_tl : v ∉ tl := fun h_in ↦ hv_not_tail (by rw [hv]; exact h_in)
      simp [List.count_cons_self, List.count_eq_zero.mpr h_tl]

  -- 2. Deduce v must appear in the prefix dropLast
  have hv_in_p1 : v ∈ p₁.vertices.dropLast := by
    have h2 : 2 ≤ (p₁.vertices.dropLast ++ p₂.vertices).count v := by
      simpa [← vertices_comp, ← hp] using hv_ge₂
    rw [List.count_append, h_p2_count] at h2
    exact List.count_pos_iff.mp (by omega)

  -- 3. Extract the sub-prefix up to the first occurrence of v
  have hv_mem_p1 := List.mem_of_mem_dropLast hv_in_p1
  obtain ⟨v', q, c, _, h_q_len, hv'_eq⟩ := split_at_vertex p₁ _ (List.idxOf_lt_length_of_mem hv_mem_p1)
  rcases hv'_eq.trans (List.get_idxOf_of_mem hv_mem_p1) with rfl

  -- 4. The new path `q ⟶ p₂` is strictly shorter
  have h_shorter : (q.comp p₂).length < p.length := calc
    (q.comp p₂).length = q.length + p₂.length := length_comp q p₂
    _ < p₁.length + p₂.length := by
      apply Nat.add_lt_add_right
      rw [h_q_len, idxOf_eq_idxOf_of_isPrefix (dropLast_prefix p₁.vertices) hv_in_p1]
      have h_lt := List.idxOf_lt_length_of_mem hv_in_p1
      revert h_lt
      simp [List.length_dropLast, vertices_length]
    _ = p.length := by rw [hp, length_comp]
  grind

/-- The length of a strictly simple path is at most one less than the number of vertices in the graph. -/
lemma length_le_card_minus_one_of_isSimple {n : Type*} [Fintype n] [DecidableEq n] [Quiver n]
     {a b : n} (p : Path a b) (hp : p.IsStrictlySimple) :
    p.length ≤ Fintype.card n - 1 := by
  have h_card_verts : p.vertexFinset.card = p.length + 1 := card_vertexFinset_of_isStrictlySimple hp
  have h_card_le_univ : p.vertexFinset.card ≤ Fintype.card n := Finset.card_le_univ p.vertexFinset
  rw [h_card_verts] at h_card_le_univ
  exact Nat.le_sub_one_of_lt h_card_le_univ


/-! Cycles -/

/-- A path is simple if it does not visit any vertex more than once, with the possible
exception of the final vertex, which may be the same as the start vertex in a cycle. -/
def IsSimple {a b : V} (p : Path a b) : Prop :=
  p.vertices.dropLast.Nodup

/-- A cycle is a non-trivial path from a vertex back to itself that does not repeat vertices,
except for the start/end vertex. -/
@[nolint unusedArguments]
def IsCycle {a : V} (p : Path a a) : Prop :=
  p.length > 0 ∧ IsSimple p

lemma isSimple_of_isStrictlySimple {a b : V} {p : Path a b} (h : IsStrictlySimple p) : IsSimple p := by
  unfold IsSimple IsStrictlySimple at *
  simpa using h.sublist (List.dropLast_sublist (l := p.vertices))

/-!
# Acyclic Quivers

This module defines acyclic quivers and proves that a quiver is acyclic if and only if it
contains no simple cycles.

## Main definitions

* `Quiver.IsAcyclic`: A typeclass indicating that a quiver has no non-trivial paths from a
  vertex to itself.
* `Quiver.IsCycle`: A predicate on a path indicating it is a simple cycle.

## Main results

* `isAcyclic_iff_no_cycles`: A quiver is acyclic iff it contains no simple cycles.

-/

section Acyclic

variable {V : Type*} [Quiver V]

/-- A quiver is acyclic if there are no non-trivial paths from a vertex to itself. -/
class IsAcyclic (V : Type*) [Quiver V] : Prop where
  /-- The defining property of an acyclic quiver: any path from a vertex `a` to itself
  must have length zero. -/
  acyclic : ∀ (a : V) (p : Path a a), p.length = 0

-- Expose the lemma in a more convenient form.
lemma IsAcyclic.path_eq_nil {V : Type*} [Quiver V] [IsAcyclic V] {a : V} (p : Path a a) : p = Path.nil :=
  Path.eq_nil_of_length_zero p (IsAcyclic.acyclic a p)

lemma isAcyclic_iff_length_eq_zero :
    IsAcyclic V ↔ ∀ {a : V} (p : Path a a), p.length = 0 := by
  constructor
  · intro h; exact fun {a} p ↦ IsAcyclic.acyclic a p
  · intro h; exact { acyclic := fun a p ↦ h p }

/-- If a quiver is acyclic, then it contains no simple cycles. -/
lemma isAcyclic_of_no_cycles [DecidableEq V] :
    IsAcyclic V → ∀ {a : V} (p : Path a a), ¬IsCycle p := by
  intro h_acyclic a p h_cycle
  have h_pos : p.length > 0 := h_cycle.1
  have h_zero : p.length = 0 := IsAcyclic.acyclic a p
  exact (Nat.not_lt.mpr (le_of_eq h_zero)) h_pos

/-- There exists a positive loop shorter than p if q is such a loop. -/
lemma exists_positive_loop_shorter_than_p [DecidableEq V] {a : V} {p : Path a a} (q : Path a a)
    (h_q_pos : q.length > 0) (h_q_shorter : q.length < p.length) :
    ∃ n, ∃ (r : Path a a), r.length = n ∧ r.length > 0 ∧ r.length < p.length := by
  exact ⟨q.length, q, rfl, h_q_pos, h_q_shorter⟩

open Classical


/-- For any two positive loops shorter than p, their minimum length equals
    the minimum length among all positive loops shorter than p, or there exists
    an even shorter loop. -/
lemma min_length_among_shorter_loops {a : V} {p : Path a a} (q r : Path a a)
    (h_q_pos : q.length > 0) (h_r_pos : r.length > 0)
    (h_q_shorter : q.length < p.length) (h_r_shorter : r.length < p.length) :
    min q.length r.length = Nat.find (exists_positive_loop_shorter_than_p q h_q_pos h_q_shorter) ∨
    ∃ (s : Path a a), s.length = Nat.find (exists_positive_loop_shorter_than_p q h_q_pos h_q_shorter) ∧
                     s.length > 0 ∧ s.length < p.length ∧ s.length < min q.length r.length := by
  let E := exists_positive_loop_shorter_than_p q h_q_pos h_q_shorter
  have h_le := le_min (Nat.find_min' E ⟨q, rfl, h_q_pos, h_q_shorter⟩)
    (Nat.find_min' E ⟨r, rfl, h_r_pos, h_r_shorter⟩)
  rcases h_le.eq_or_lt with h_eq | h_lt
  · exact Or.inl h_eq.symm
  · obtain ⟨s, hs_eq, hs_pos, hs_shorter⟩ := Nat.find_spec E
    exact Or.inr ⟨s, hs_eq, hs_pos, hs_shorter, hs_eq.symm ▸ h_lt⟩

/--
Among all positive-length loops shorter than `p`, `q` is minimal.
-/
lemma shortest_among_shorter_loops [DecidableEq V] {a : V} {p : Path a a} (q : Path a a)
    (_ : q.length > 0)
    (h_q_shorter : q.length < p.length)
    (h_q_minimal : ∀ r : Path a a, r.length > 0 → r.length < p.length → q.length ≤ r.length) :
    ∀ r : Path a a, r.length > 0 → q.length ≤ r.length :=
  fun r hr ↦ (Nat.lt_or_ge r.length p.length).elim (h_q_minimal r hr) h_q_shorter.le.trans

/-- If there exists any positive-length loop at `a`, then there exists a shortest one. -/
lemma exists_shortest_positive_loop [DecidableEq V] {a : V} (q : Path a a) (hq_pos : q.length > 0) :
    ∃ (s : Path a a), s.length > 0 ∧ ∀ (r : Path a a), r.length > 0 → s.length ≤ r.length := by
  let E : ∃ n, ∃ r : Path a a, r.length = n ∧ r.length > 0 := ⟨q.length, q, rfl, hq_pos⟩
  obtain ⟨s, hs_eq, hs_pos⟩ := Nat.find_spec E
  exact ⟨s, hs_pos, fun r hr ↦ hs_eq.symm ▸ Nat.find_min' E ⟨r, rfl, hr⟩⟩

/-- If n < m and m ≤ n, we have a contradiction -/
private lemma Nat.lt_le_antisymm {n m : Nat} (h1 : n < m) (h2 : m ≤ n) : False :=
  Nat.lt_irrefl n (Nat.lt_of_lt_of_le h1 h2)

/-- If n ≥ m, then it's not the case that n < m. -/
private lemma not_lt_of_ge {n m : Nat} (h : n ≥ m) : ¬(n < m) :=
  fun h' => Nat.lt_le_antisymm h' h

/-- If n > m, then it's not the case that n ≤ m -/
private lemma not_le_of_gt {n m : Nat} (h : n > m) : ¬(n ≤ m) :=
  fun h' => Nat.lt_le_antisymm h h'

/-- Given a path with a repeated vertex, we can find that vertex and show it appears
    in the dropLast portion of the prefix path. -/
lemma repeated_vertex_in_prefix_dropLast [DecidableEq V] {a : V} (s : Path a a)
    (h_not_simple : ¬IsStrictlySimple s) :
    ∃ (v : V) (p₁ : Path a v) (p₂ : Path v a),
      v ∈ p₁.vertices.dropLast ∧ s = p₁.comp p₂ ∧ v ∉ p₂.vertices.tail := by
  obtain ⟨v, hv_in, hv_ge₂⟩ := not_strictly_simple_iff_exists_repeated_vertex.mp h_not_simple
  obtain ⟨p₁, p₂, hp, hv_not_tail⟩ := exists_decomp_of_mem_vertices_prop s hv_in
  have h_p2_count : p₂.vertices.count v = 1 := by
    cases hv : p₂.vertices with
    | nil => exact (vertices_nonempty p₂ hv).elim
    | cons hd tl =>
      have h_hd : hd = v := Option.some_inj.mp (by simpa [hv] using vertices_head? p₂)
      rw [h_hd] at hv ⊢
      have h_tl : v ∉ tl := by simpa [hv] using hv_not_tail
      simp [List.count_cons_self, List.count_eq_zero.mpr h_tl]
  have hv_in_p1 : v ∈ p₁.vertices.dropLast := by
    have h_count : s.vertices.count v = (p₁.vertices.dropLast ++ p₂.vertices).count v := by
      rw [hp, vertices_comp]
    rw [h_count, List.count_append, h_p2_count] at hv_ge₂
    exact List.count_pos_iff.mp (by omega)
  exact ⟨v, p₁, p₂, hv_in_p1, hp, hv_not_tail⟩


lemma extract_cycle_from_prefix [DecidableEq V] {a vertex : V} {p₁ : Path a vertex}
    (h_in_drop : vertex ∈ p₁.vertices.dropLast) :
    ∃ (q : Path a vertex) (c : Path vertex vertex),
      p₁ = q.comp c ∧ vertex ∉ q.vertices.dropLast := by
  let i := p₁.vertices.idxOf vertex
  have h_mem := List.mem_of_mem_dropLast h_in_drop
  obtain ⟨v, q, c, h_comp, h_len, h_v⟩ := split_at_vertex p₁ i (List.idxOf_lt_length_of_mem h_mem)
  rcases h_v.trans (List.get_idxOf_of_mem h_mem) with rfl
  refine ⟨q, c, h_comp, fun h ↦ ?_⟩
  -- Correctly proving the prefix for the index lemma
  have h_pre : q.vertices.dropLast <+: p₁.vertices := by
    rw [h_comp, vertices_comp]
    grind
  have h_idx := List.idxOf_eq_idxOf_of_isPrefix h_pre h
  have h_lt := List.idxOf_lt_length_of_mem h
  rw [← h_idx, List.length_dropLast, vertices_length] at h_lt
  grind

lemma extract_cycle_from_prefix' [DecidableEq V] {a v : V} {p₁ : Path a v}
    (hv_in_p1_dropLast : v ∈ p₁.vertices.dropLast) :
    ∃ (q : Path a v) (c : Path v v),
      p₁ = q.comp c := by
  obtain ⟨q, c, h_split⟩ :=
    exists_decomp_of_mem_vertices p₁ (List.mem_of_mem_dropLast hv_in_p1_dropLast)
  exact ⟨q, c, h_split⟩

/-- A cycle extracted from a path with a repeated vertex has positive length. -/
lemma extracted_cycle_has_positive_length [DecidableEq V] {a v : V}
    {p₁ q : Path a v} {c : Path v v}
    (h_p1_split : p₁ = q.comp c)
    (hv_in_p1_dropLast : v ∈ p₁.vertices.dropLast)
    (hv_not_in_q : v ∉ q.vertices.dropLast) : c.length > 0 := by
  by_cases h_len_zero : c.length = 0
  · have hc_nil : c = Path.nil := (length_eq_zero_iff c).mp h_len_zero
    have h_p1_eq_q : p₁ = q := by
      rw [h_p1_split, hc_nil, comp_nil]
    have h_v_in_q : v ∈ q.vertices.dropLast := by
      subst h_p1_eq_q
      exact hv_in_p1_dropLast
    exact False.elim (hv_not_in_q h_v_in_q)
  · exact Nat.pos_of_ne_zero h_len_zero

/-- Removing a cycle from a path creates a strictly shorter path. -/
lemma removing_cycle_gives_shorter_path [DecidableEq V] {a v : V} {s : Path a a}
    {q : Path a v} {c : Path v v} {p₂ : Path v a}
    (hp : s = (q.comp c).comp p₂) (hc_pos : c.length > 0) : (q.comp p₂).length < s.length := by
  have h_len_shorter : (q.comp p₂).length = q.length + p₂.length := by
    rw [length_comp]
  have h_len_s : s.length = q.length + c.length + p₂.length := by
    rw [hp, comp_assoc, length_comp, length_comp]
    ring
  rw [h_len_shorter, h_len_s]
  subst hp
  simp_all only [le_refl, gt_iff_lt, length_comp, comp_assoc, add_lt_add_iff_right,
    lt_add_iff_pos_right, Nat.eq_of_le_zero]

/-
/-- A shortest positive loop is strictly simple. -/
theorem shortest_positive_loop_is_strictly_simple {a : V} :
    ∀ (c : Path a a), c.length > 0 → (∀ p' : Path a a, p'.length > 0 → c.length ≤ p'.length) →
    c.IsStrictlySimple := by sorry
-/
