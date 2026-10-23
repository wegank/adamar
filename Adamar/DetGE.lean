/-
Copyright (c) 2026 Weijia Wang. All rights reserved.
-/
import Mathlib

/-!
# A verified determinant by Gaussian elimination

The determinant `Matrix.det` of Mathlib is computable, but it is defined as a sum over all
permutations, so its evaluation takes factorial time. For the executable version of the sign
determination algorithm, we define `Adamar.detGE`, which computes the determinant of a matrix
over a field by Gaussian elimination (with a cubic number of field operations), and we prove
that it agrees with `Matrix.det` (`Adamar.detGE_eq_det`).
-/

namespace Adamar

open Matrix

variable {K : Type*} [Field K]

/-- One step of Gaussian elimination: the Schur complement of the top-left entry. -/
def schurStep {m : ℕ} (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Matrix (Fin m) (Fin m) K :=
  Matrix.of fun i j => B i.succ j.succ - B i.succ 0 / B 0 0 * B 0 j.succ

/-- Expanding the determinant with respect to a non-zero top-left entry. -/
lemma det_eq_mul_det_schurStep {m : ℕ} (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (h : B 0 0 ≠ 0) : B.det = B 0 0 * (schurStep B).det := by
  set c := B 0 0 with hc
  -- The lower triangular unipotent matrix performing the elimination in the first column.
  let E : Matrix (Fin (m + 1)) (Fin (m + 1)) K := Matrix.of fun i j =>
    (if i = j then 1 else 0) - (if j = 0 ∧ i ≠ 0 then B i 0 / c else 0)
  have hE : E.det = 1 := by
    rw [det_of_isLowerTriangular]
    · simp [E]
    · intro i j hij
      rw [OrderDual.toDual_lt_toDual] at hij
      have h1 : i ≠ j := ne_of_lt hij
      have h2 : j ≠ 0 := Fin.pos_iff_ne_zero.1 (lt_of_le_of_lt (Fin.zero_le _) hij)
      simp [E, h1, h2]
  have hEB : E * B = Matrix.of fun i j =>
      if i = 0 then B 0 j else B i j - B i 0 / c * B 0 j := by
    ext i j
    simp only [mul_apply, E, of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ite_and, Finset.sum_ite_eq']
    by_cases hi : i = 0 <;> simp [hi]
  rw [← one_mul B.det, ← hE, ← det_mul, hEB, det_succ_column_zero, Fin.sum_univ_succ]
  rw [Finset.sum_eq_zero fun i _ => ?_]
  · simp only [Fin.val_zero, pow_zero, one_mul, of_apply, ite_true, add_zero, Fin.succAbove_zero]
    congr 2
  · simp [Fin.succ_ne_zero, ← hc, div_mul_cancel₀ _ h]

variable [DecidableEq K]

/-- The index of the first non-zero entry of a column, if any. -/
def pivot? {m : ℕ} (col : Fin m → K) : Option (Fin m) :=
  (List.finRange m).find? fun i => col i ≠ 0

lemma pivot?_eq_none {m : ℕ} {col : Fin m → K} : pivot? col = none ↔ ∀ i, col i = 0 := by
  simp [pivot?, List.find?_eq_none]

lemma pivot?_some {m : ℕ} {col : Fin m → K} {p : Fin m} (h : pivot? col = some p) :
    col p ≠ 0 := by
  simpa using List.find?_some h

/-- The determinant of a square matrix over a field, computed by Gaussian elimination with
pivot search in the first column. -/
def detGE : {m : ℕ} → Matrix (Fin m) (Fin m) K → K
  | 0, _ => 1
  | _ + 1, A =>
    match pivot? fun i => A i 0 with
    | none => 0
    | some p =>
      let B := A.submatrix (Equiv.swap 0 p) id
      (if p = 0 then 1 else -1) * B 0 0 * detGE (schurStep B)

/-- Gaussian elimination computes the determinant. -/
theorem detGE_eq_det {m : ℕ} (A : Matrix (Fin m) (Fin m) K) : detGE A = A.det := by
  induction m with
  | zero => simp [detGE]
  | succ m ih =>
    unfold detGE
    split
    · next hnone =>
      exact (det_eq_zero_of_column_eq_zero 0 (pivot?_eq_none.1 hnone)).symm
    · next p hp =>
      have hp0 : A p 0 ≠ 0 := pivot?_some (col := fun i => A i 0) hp
      set B := A.submatrix (Equiv.swap 0 p) id with hB
      have hB0 : B 0 0 ≠ 0 := by simpa [hB] using hp0
      have hdet : B.det = ((Equiv.Perm.sign (Equiv.swap 0 p) : ℤ) : K) * A.det := det_permute _ _
      dsimp only
      rw [ih, mul_assoc, ← det_eq_mul_det_schurStep B hB0, hdet]
      by_cases h : p = 0
      · subst h
        simp
      · rw [Equiv.Perm.sign_swap (Ne.symm h)]
        simp [h]

/-! ### An implementation on arrays

Since matrices are functions, the matrices built by `detGE` are recomputed at each access to
their entries. We therefore run the same algorithm on arrays of arrays. -/

/-- Reading an entry of an array of arrays, with default value `0`. -/
def arrGet (a : Array (Array K)) (i j : ℕ) : K := (a.getD i #[]).getD j 0

/-- The array of arrays of the entries of a matrix. -/
def toArr {m : ℕ} (A : Matrix (Fin m) (Fin m) K) : Array (Array K) :=
  Array.ofFn fun i => Array.ofFn fun j => A i j

omit [DecidableEq K] in
@[simp] lemma arrGet_toArr {m : ℕ} (A : Matrix (Fin m) (Fin m) K) (i j : Fin m) :
    arrGet (toArr A) i j = A i j := by
  simp [arrGet, toArr, Array.getD]

/-- `detGE`, running on arrays of arrays. -/
def detArr : ℕ → Array (Array K) → K
  | 0, _ => 1
  | m + 1, a =>
    match pivot? fun i : Fin (m + 1) => arrGet a i 0 with
    | none => 0
    | some p =>
      let B : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
        Matrix.of fun i j => arrGet a (Equiv.swap 0 p i) j
      (if p = 0 then 1 else -1) * B 0 0 * detArr m (toArr (schurStep B))

lemma detArr_eq_detGE (m : ℕ) (a : Array (Array K)) :
    detArr m a = detGE (Matrix.of fun i j : Fin m => arrGet a i j) := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    unfold detArr detGE
    simp only [of_apply, Fin.val_zero]
    rcases pivot? fun i : Fin (m + 1) => arrGet a i 0 with _ | p
    · rfl
    · dsimp only
      rw [ih]
      have hB : (Matrix.of fun i j : Fin m => arrGet (toArr (schurStep (Matrix.of fun i j =>
          arrGet a (Equiv.swap 0 p i) j))) i j) =
          schurStep ((Matrix.of fun i j : Fin (m + 1) => arrGet a i j).submatrix
            (Equiv.swap 0 p) id) := by
        ext i j
        simp [schurStep]
      rw [hB]
      rfl

/-- A determinant computed in a cubic number of field operations. -/
def detFast {m : ℕ} (A : Matrix (Fin m) (Fin m) K) : K := detArr m (toArr A)

theorem detFast_eq_det {m : ℕ} (A : Matrix (Fin m) (Fin m) K) : detFast A = A.det := by
  rw [detFast, detArr_eq_detGE, ← detGE_eq_det]
  congr 1
  ext i j
  simp

end Adamar
