/-
Copyright (c) 2026 Weijia Wang. All rights reserved.
-/
import Adamar.Adapt

/-!
# Examples from the book

We check, by evaluation in the kernel, that `Adamar.adapt` computes the adapted families of
Examples 10.74 and 10.81 of *Algorithms in Real Algebraic Geometry* (Basu, Pollack, Roy).

Two conventions differ from the book:
* signs `0, 1, -1` are encoded as `0, 1, 2 : Fin 3`, exponents `0, 1, 2` are themselves;
* the book splits a list of polynomials `P₁, …, Pₛ` along its *last* element, while `adapt`
  splits a tuple along its *first* coordinate. Hence a sign condition `(σ(P₁), …, σ(Pₛ))` of
  the book is represented by the tuple `![σ(Pₛ), …, σ(P₁)]`.
-/

namespace Adamar

/-- Builds a set of tuples from the *columns* of a matrix, given as rows `P₁, …, Pₛ` of the
book, reversing the order of the coordinates (see the module docstring). -/
def ofBookRows {s : ℕ} (rows : Fin s → List (Fin 3)) (m : ℕ) : Finset (Fin s → Fin 3) :=
  ((List.range m).map fun j i => (rows (Fin.rev i)).getD j 0).toFinset

/-! ### Example 10.74: a single polynomial -/

example : adapt (k := 3) (n := 1) {![0], ![1], ![2]} = {![0], ![1], ![2]} := by decide
example : adapt (k := 3) (n := 1) {![1], ![2]} = {![0], ![1]} := by decide
example : adapt (k := 3) (n := 1) {![0], ![1]} = {![0], ![1]} := by decide
example : adapt (k := 3) (n := 1) {![0], ![2]} = {![0], ![1]} := by decide
example : adapt (k := 3) (n := 1) {![2]} = {![0]} := by decide

/-! ### Example 10.81: four polynomials and eleven sign conditions -/

/-- The set `Σ` of Example 10.81 (`2` stands for the sign `-1`). -/
def sigma1081 : Finset (Fin 4 → Fin 3) :=
  ofBookRows ![[0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2],
               [1, 1, 1, 1, 2, 2, 2, 0, 0, 0, 0],
               [0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1],
               [0, 1, 2, 2, 0, 1, 2, 0, 2, 1, 2]] 11

/-- The adapted family `Ada(Σ)` computed in Example 10.81. -/
def ada1081 : Finset (Fin 4 → Fin 3) :=
  ofBookRows ![[0, 1, 2, 0, 1, 0, 1, 2, 0, 0, 1],
               [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
               [0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0],
               [0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2]] 11

example : sigma1081.card = 11 := by decide

/-- `adapt` computes the adapted family of Example 10.81. -/
theorem adapt_sigma1081 : adapt sigma1081 = ada1081 := by decide

/- The elements of `Ada(Σ)` as exponent vectors `(α(P₁), α(P₂), α(P₃), α(P₄))`, i.e. the list
`1, P₁, P₁², P₃, P₁P₃, P₄, P₁P₄, P₁²P₄, P₃P₄, P₄², P₁P₄²` of the book. -/
/--
info: {[0, 0, 0, 0],
 [1, 0, 0, 0],
 [2, 0, 0, 0],
 [0, 0, 1, 0],
 [1, 0, 1, 0],
 [0, 0, 0, 1],
 [1, 0, 0, 1],
 [2, 0, 0, 1],
 [0, 0, 1, 1],
 [0, 0, 0, 2],
 [1, 0, 0, 2]}
-/
#guard_msgs in
#eval (adapt sigma1081).image fun f => List.ofFn fun i => (f (Fin.rev i) : ℕ)

/-- The recursive calls of Example 10.81: `Ξ(0)`, `Ξ(1)` and `Ξ(2)`. -/
example : Xi 0 sigma1081 = ofBookRows ![[0, 0, 1, 2, 2], [1, 1, 2, 0, 0], [0, 1, 0, 0, 1]] 5 := by
  decide
example : Xi 1 sigma1081 = ofBookRows ![[0, 1, 2, 2], [1, 2, 0, 0], [0, 0, 0, 1]] 4 := by
  decide
example : Xi 2 sigma1081 = ofBookRows ![[0, 1], [1, 2], [0, 0]] 2 := by
  decide

/-- As predicted by Proposition 10.84, every element of `Ada(Σ)` has at most
`log₂ 11 = 3` non-zero entries (here, at most `2`). -/
example : ∀ a ∈ ada1081, (Finset.univ.filter fun i => a i ≠ 0).card ≤ 2 := by decide

end Adamar
