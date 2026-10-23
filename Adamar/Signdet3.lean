/-
Copyright (c) 2026 Weijia Wang. All rights reserved.
Portions copyright (c) 2014 Cyril Cohen (Coq development `signdet.v`), used under the MIT
license as described in the file LICENSE.
-/
import Adamar.Adapt

/-!
# Instantiation to sign determination

This file is the Lean counterpart of the section `Signdet3` of `signdet.v`.

We encode the bijection between `Fin 3` and the signs `{0, 1, -1}` by `Adamar.sign`, and
define the matrix
```
          ⎛ 1  0  0 ⎞
ctmat3 =  ⎜ 1  1  1 ⎟ ,   ctmat3 i j = (sign i) ^ j.
          ⎝ 1 -1  1 ⎠
```
whose `(σ, α)` entry is the sign of `Q ^ α` at a point where `Q` has sign `σ`.

In Coq, the invertibility of every leftmost square submatrix of `ctmat3` is checked by
computing determinants by hand. Here we instead observe that the leftmost submatrices of any
matrix of the form `(x i ^ j)` with pairwise distinct `x i` are Vandermonde matrices
(`Adamar.rowFree_mat1_vandermonde`), so that the theory of adapted families applies to any
such matrix (`Adamar.vandermonde_adapted`). We nonetheless also give the explicit
determinants computed in the Coq development.
-/

namespace Adamar

open Finset Matrix

section Vandermonde

variable {F : Type*} [Field F] {k : ℕ}

/-- The `k × k` matrix `(x i ^ j)`, i.e. `Matrix.vandermonde x`. -/
def powMatrix (x : Fin k → F) : Matrix (Fin k) (Fin k) F := Matrix.of fun i j => x i ^ (j : ℕ)

lemma powMatrix_eq_vandermonde (x : Fin k → F) : powMatrix x = Matrix.vandermonde x := by
  ext i j
  simp [powMatrix]

/-- Reindexing the rows of a matrix along an equivalence does not change row-freeness. -/
lemma rowFree_submatrix_equiv_iff {m m' n : Type*} (A : Matrix m n F) (e : m' ≃ m) :
    RowFree (A.submatrix e id) ↔ RowFree A :=
  linearIndependent_equiv e

/-- All the leftmost square submatrices of `(x i ^ j)` are invertible when the `x i` are
pairwise distinct, as they are Vandermonde matrices. -/
theorem rowFree_mat1_vandermonde {x : Fin k → F} (hx : Function.Injective x)
    (S : Finset (Fin k)) : RowFree (mat1 (powMatrix x) S) := by
  let e : Fin S.card ≃ S := S.equivFin.symm
  rw [← rowFree_submatrix_equiv_iff _ e]
  have : (mat1 (powMatrix x) S).submatrix e id = Matrix.vandermonde (fun i => x (e i)) := by
    ext i j
    simp [mat1, powMatrix]
  rw [this, rowFree_iff_det_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
  exact hx.comp (Subtype.val_injective.comp e.injective)

/-- For pairwise distinct `x i`, the family `adapt S` is adapted to `S` for the matrix
`(x i ^ j)`. This generalizes `Adamar.ctmat_adapted` to "sign conditions" with `k` values. -/
theorem vandermonde_adapted {x : Fin k → F} (hx : Function.Injective x) {n : ℕ}
    (S : Finset (Fin n → Fin k)) : adapted (powMatrix x) S (adapt S) :=
  adapt_adapted (rowFree_mat1_vandermonde hx) S

end Vandermonde

/-- The bijection between `Fin 3` and the signs `{0, 1, -1}`. -/
def sign (k : Fin 3) : ℚ := if 2 ≤ (k : ℕ) then -1 else (k : ℕ)

@[simp] lemma sign_zero : sign 0 = 0 := rfl
@[simp] lemma sign_one : sign 1 = 1 := rfl
@[simp] lemma sign_two : sign 2 = -1 := by simp [sign]

lemma sign_injective : Function.Injective sign := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [sign] <;> norm_num at h

/-- The matrix of signs of `1, Q, Q²` on the sign conditions `0, 1, -1`. -/
def ctmat3 : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of fun i j => sign i ^ (j : ℕ)

/-- The `2 × 2` matrix obtained from `ctmat3` by removing the row `k` and the last column. -/
def ctmat2 (k : Fin 3) : Matrix (Fin 2) (Fin 2) ℚ :=
  Matrix.of fun i j => sign (k.succAbove i) ^ (j : ℕ)

lemma ctmat3_eq : ctmat3 = !![1, 0, 0; 1, 1, 1; 1, -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ctmat3]

lemma ctmat3_eq_powMatrix : ctmat3 = powMatrix sign := rfl

/-- Coq: `det_ctmat2`. -/
lemma det_ctmat2 (k : Fin 3) :
    (ctmat2 k).det = if (k : ℕ) ≤ 0 then -2 else if 1 < (k : ℕ) then 1 else -1 := by
  fin_cases k <;> norm_num [ctmat2, Matrix.det_fin_two, Fin.succAbove]

/-- Coq: `det_ctmat3`. -/
lemma det_ctmat3 : ctmat3.det = 2 := by
  rw [ctmat3_eq, Matrix.det_fin_three]
  norm_num

/-- Coq: `row_free_ctmat`. -/
theorem row_free_ctmat (S : Finset (Fin 3)) : RowFree (mat1 ctmat3 S) :=
  rowFree_mat1_vandermonde sign_injective S

/-- Coq: `ctmat_adapted`. -/
theorem ctmat_adapted {n : ℕ} (S : Finset (Fin n → Fin 3)) : adapted ctmat3 S (adapt S) :=
  adapt_adapted row_free_ctmat S

end Adamar
