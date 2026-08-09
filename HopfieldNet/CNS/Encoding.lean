/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HopfieldNet.CNS.Reduce

/-!
# The QUBO encoding

Li & Wang encode Sudoku as the unconstrained minimisation of

  `p(x̄) = ½‖A_a x̄ − e‖² + ½‖A_b x̄ − e‖² + ½‖A_c x̄ − e‖² + ½‖A_d x̄ − e‖²`   (11a)-(11d)

over `x̄ ∈ {0,1}^{n³}`, and then solve it with dynamics of the form (1)-(3) and (5)-(6), whose
canonical objective is

  `min −½ x^T W x + θ^T x`                                                        (4)

but they never write down `W` or `θ`. This module supplies the missing derivation and makes it
executable.

## Deviation from the printed formulae

Equation (12) reads `p = p_b + p_c + p_d + p_e`, but (11) defines only `p_a … p_d`; §IV then
speaks of `Â_b … Â_e`. The index has slipped by one: the intended objective is the sum over all
four constraint families, which is what `A` below stacks. Separately, the Σ-expressions in
(11b), (11c) and (11d) are missing a `Σ_k` and produce `n` terms where `n²` are required; the
matrix forms `½‖A· x̄ − e_{n²}‖²` are the correct statements and are the ones implemented here.

## The derivation

Stack the four families into `A ∈ {0,1}^{4n² × n³}` with right-hand side `b = e`. Then

  `p(x) = ½‖Ax − b‖² = ½ xᵀ(AᵀA)x − bᵀAx + ½‖b‖²`.

Two structural facts, both verified by `cns encoding`:

* every column of `A` has exactly **4** nonzeros — variable `x_{ijk}` occurs in exactly one cell
  constraint, one column constraint, one row constraint and one block constraint — hence
  `diag(AᵀA) = 4`;
* every row of `A` has exactly `n = 9` nonzeros.

Because `x` is binary, `x_v² = x_v`, so the diagonal of `AᵀA` may be moved into the linear term.
Matching against (4) gives

  `W = −(AᵀA − 4I)`,     `θ = −Aᵀb + 2`,     `p(x) = −½xᵀWx + θᵀx + ½‖b‖²`.

For the unreduced puzzle `b = e`, so `Aᵀb = 4` and `θ = −2` uniformly, with `½‖b‖² = 162`.
Crucially `W` is symmetric with **zero diagonal**, which is exactly the predicate
`pm W = W.IsSymm ∧ ∀ u, W u u = 0` that `TwoState.ZeroOne` demands of its weight matrix.

The 4-nonzeros-per-column structure also means `Wx = −(Aᵀ(Ax) − 4x)` costs `O(n³)` rather than
`O(n⁶)`; each variable has exactly 28 off-diagonal neighbours, with couplings in `{1,2}`.
-/

namespace CNS

/-! ## Row layout of the stacked matrix `A` -/

/-- Row of the cell constraint (11a) for cell `(i,j)`: `Σ_k x_{ijk} = 1`. -/
@[inline] def rowCell (i j : Nat) : Nat := cellIdx i j

/-- Row of the column constraint (11b) for column `j`, digit `k`: `Σ_i x_{ijk} = 1`. -/
@[inline] def rowCol (j k : Nat) : Nat := n * n + j * n + k

/-- Row of the row constraint (11c) for row `i`, digit `k`: `Σ_j x_{ijk} = 1`. -/
@[inline] def rowRow (i k : Nat) : Nat := 2 * n * n + i * n + k

/-- Row of the block constraint (11d) for block `b`, digit `k`. -/
@[inline] def rowBox (b k : Nat) : Nat := 3 * n * n + b * n + k

/-- The four rows of `A` in which `x_{ijk}` has a nonzero entry. -/
def rowsOfVar (v : Nat) : Array Nat :=
  let i := v / (n * n)
  let j := (v % (n * n)) / n
  let k := v % n
  #[rowCell i j, rowCol j k, rowRow i k, rowBox (boxOf (cellIdx i j)) k]

/-- The `n` variables occurring in each of the `4n²` rows of `A`. -/
def varsOfRow : Array (Array Nat) := Id.run do
  let mut rows : Array (Array Nat) := Array.replicate numRows #[]
  for v in [0:numVars] do
    for r in rowsOfVar v do
      rows := rows.set! r ((rows.getD r #[]).push v)
  return rows

/-! ## The penalty -/

/-- Encode a complete grid as the binary vector `x̄ ∈ {0,1}^{n³}`. -/
def encode (g : Grid) : Array Bool := Id.run do
  let mut x : Array Bool := Array.replicate numVars false
  for c in [0:numCells] do
    if let some k := g.get c then
      x := x.set! (varIdx (rowOf c) (colOf c) k) true
  return x

/-- Decode `x̄` back to a grid; a cell with anything other than exactly one `1` is left empty. -/
def decode (x : Array Bool) : Grid := Id.run do
  let mut cells : Array (Option Nat) := Array.replicate numCells none
  for c in [0:numCells] do
    let i := rowOf c
    let j := colOf c
    let hits := (Array.range n).filter fun k => x.getD (varIdx i j k) false
    if hits.size == 1 then
      cells := cells.set! c (hits[0]?)
  return ⟨cells⟩

/-! ### The constraint rows, by explicit formula

`varsOfRow` above is built by accumulating over variables, which is convenient to compute and
impossible to reason about. The following give the same four families directly, so that a
theorem about `rowCount` is visibly a theorem about (10a)-(10d). `cns encoding` checks that the
two agree, via `specMatchesTable`. -/

/-- (10a) The `n` variables of cell `(i,j)`: the digits that cell may hold. -/
def cellVars (i j : Nat) : List Nat := (List.range n).map (fun k => varIdx i j k)

/-- (10b) The `n` variables placing digit `k` somewhere in column `j`. -/
def colVars (j k : Nat) : List Nat := (List.range n).map (fun i => varIdx i j k)

/-- (10c) The `n` variables placing digit `k` somewhere in row `i`. -/
def rowVars (i k : Nat) : List Nat := (List.range n).map (fun j => varIdx i j k)

/-- (10d) The `n` variables placing digit `k` somewhere in block `b`. -/
def boxVars (b k : Nat) : List Nat :=
  (List.range n).map (fun t => varIdx ((b / blk) * blk + t / blk) ((b % blk) * blk + t % blk) k)

/-- Constraint row `r` as an explicit member of one of the four families. -/
def varsOfRowSpec (r : Nat) : List Nat :=
  if r < n * n then cellVars (r / n) (r % n)
  else if r < 2 * n * n then colVars ((r - n * n) / n) ((r - n * n) % n)
  else if r < 3 * n * n then rowVars ((r - 2 * n * n) / n) ((r - 2 * n * n) % n)
  else boxVars ((r - 3 * n * n) / n) ((r - 3 * n * n) % n)

/-- How many of the listed variables `x` sets. -/
def countOn (x : Array Bool) (l : List Nat) : Int :=
  l.foldl (fun acc v => if x.getD v false then acc + 1 else acc) 0

/-- How many variables of constraint row `r` the assignment `x` sets.

For a cell row this is the number of digits written in that cell; for a row, column or block
row it is the number of times that digit occurs in that unit. Every constraint of (10a)-(10d)
demands the value `1`. -/
@[inline] def rowCount (x : Array Bool) (r : Nat) : Int := countOn x (varsOfRowSpec r)

/-- The residual `(Ax − b)_r` of row `r`, with `b = e`. -/
@[inline] def residual (x : Array Bool) (r : Nat) : Int := rowCount x r - 1

/-- `‖Ax − b‖²`, i.e. **twice** the paper's `p(x̄)`.

Working with the doubled value keeps the whole objective in `Int`; `p(x) = 0` iff this is `0`. -/
def penaltyDoubled (x : Array Bool) : Int :=
  (List.range numRows).foldl (fun acc r => acc + residual x r * residual x r) 0

/-- The paper's `p(x̄) = ½‖Ax̄ − e‖²`, as a rational written `num / 2`. -/
def penaltyHalves (x : Array Bool) : Int := penaltyDoubled x

/-! ## `W` and `θ` -/

/-- `(AᵀA)_{uv}`: the number of rows containing both `u` and `v`. -/
def gram (u v : Nat) : Int :=
  (rowsOfVar u).foldl (fun acc r => if (rowsOfVar v).contains r then acc + 1 else acc) 0

/-- `W_{uv} = −(AᵀA − 4I)_{uv}`: symmetric, zero diagonal, entries in `{0, −1, −2}`. -/
def weight (u v : Nat) : Int := if u == v then 0 else -(gram u v)

/-- `θ_v = −(Aᵀb)_v + ½·diag(AᵀA)_v`. With `b = e` this is `−4 + 2 = −2` for every `v`. -/
def theta (v : Nat) : Int := -((rowsOfVar v).size : Int) + 2

/-- The additive constant `½‖b‖²` relating the canonical form to `p`. With `b = e` over `4n²`
rows this is `2n² = 162`. -/
def penaltyConst : Int := numRows

/-! ## Structural checks

`cns encoding` runs these: the facts the derivation rests on, plus the identity
`‖Ax − b‖² = −xᵀWx + 2θᵀx + ‖b‖²` (the doubled form of (4)) on supplied assignments. -/

/-- `−xᵀWx + 2θᵀx + ‖b‖²`, the canonical objective in doubled form. -/
def canonicalDoubled (x : Array Bool) : Int := Id.run do
  let on := (Array.range numVars).filter fun v => x.getD v false
  let quad := on.foldl (fun acc u => acc + on.foldl (fun a v => a + weight u v) 0) 0
  let lin := on.foldl (fun acc v => acc + theta v) 0
  return 2 * lin + penaltyConst - quad

/-- Every column of `A` has exactly four nonzeros. -/
def colsHave4 : Bool := (Array.range numVars).all fun v => (rowsOfVar v).size == 4

/-- Every row of `A` has exactly `n` nonzeros. -/
def rowsHaveN : Bool := (Array.range numRows).all fun r => (varsOfRow.getD r #[]).size == n

/-- `W` is symmetric. Checked on the `28`-neighbourhood structure rather than all `n⁶` pairs. -/
def weightSymm : Bool :=
  (Array.range numVars).all fun u =>
    (rowsOfVar u).all fun r =>
      (varsOfRow.getD r #[]).all fun v => weight u v == weight v u

/-- `W` has zero diagonal — the condition `TwoState.ZeroOne` imposes via `pm`. -/
def weightDiagZero : Bool := (Array.range numVars).all fun v => weight v v == 0

/-- The loop-built `varsOfRow` agrees with the explicit `varsOfRowSpec` on every row (up to
order), which is what lets the soundness theorem in `CNS.Sound` speak about (10a)-(10d). -/
def specMatchesTable : Bool :=
  (Array.range numRows).all fun r =>
    let a := (varsOfRow.getD r #[]).qsort (· < ·)
    let b := (varsOfRowSpec r).toArray.qsort (· < ·)
    a == b

/-- Off-diagonal neighbour count of a variable; the derivation predicts `28` for every `v`. -/
def neighbourCount (v : Nat) : Nat :=
  ((rowsOfVar v).foldl (fun acc r =>
    (varsOfRow.getD r #[]).foldl (fun a u =>
      if u == v || a.contains u then a else a.push u) acc) #[]).size

end CNS
