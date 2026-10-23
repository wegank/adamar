/-
Copyright (c) 2026 Weijia Wang. All rights reserved.
-/
import Adamar.Algorithm
import Adamar.DetGE

/-!
# An executable sign determination algorithm

The algorithm `Adamar.signDet` of `Adamar.Algorithm` is not computable, because it uses the
inverse `Adamar.adaptInv` of `Mat(C, Ada(C))`, obtained by choice. Here we define an
executable variant `Adamar.signDetExec`, which solves the linear systems by Cramer's rule
with determinants computed by Gaussian elimination (`Adamar.detFast`), and we prove that it
computes the same results as `Adamar.signDet` *for every black box*
(`Adamar.signDetExec_eq`, `Adamar.countDetExec_eq`). Its correctness is thus inherited from
`Adamar.signDet_correct` (see `Adamar.signDetExec_correct`).
-/

namespace Adamar

open Finset Matrix

section enum

variable {α : Type*} [FinEnum α] [DecidableEq α]

/-- The elements of a finset of an enumerable type, in the order of `FinEnum.toList`. -/
def enumList (s : Finset α) : List α := (FinEnum.toList α).filter (· ∈ s)

lemma nodup_enumList (s : Finset α) : (enumList s).Nodup :=
  FinEnum.nodup_toList.filter _

@[simp] lemma mem_enumList {s : Finset α} {a : α} : a ∈ enumList s ↔ a ∈ s := by
  simp [enumList, FinEnum.mem_toList]

lemma length_enumList (s : Finset α) : (enumList s).length = s.card := by
  rw [← List.toFinset_card_of_nodup (nodup_enumList s)]
  congr 1
  ext a
  simp

/-- The `i`-th element of a finset in the order of `enumList`. -/
def enumGet (s : Finset α) (i : Fin s.card) : α :=
  (enumList s).get (i.cast (length_enumList s).symm)

lemma enumGet_mem (s : Finset α) (i : Fin s.card) : enumGet s i ∈ s :=
  mem_enumList.1 (List.get_mem _ _)

lemma enumGet_injective (s : Finset α) : Function.Injective (enumGet s) := fun i j h => by
  have := (nodup_enumList s).get_inj_iff.1 h
  exact Fin.ext (by simpa using congr_arg Fin.val this)

lemma getD_enumList (s : Finset α) (d : α) (i : Fin s.card) :
    (enumList s).getD i d = enumGet s i := by
  rw [List.getD_eq_getElem _ _ (by rw [length_enumList]; exact i.2)]
  rfl

lemma getElem?_getD_enumList (s : Finset α) (d : α) (i : Fin s.card) :
    ((enumList s)[(i : ℕ)]?).getD d = enumGet s i := by
  rw [← List.getD_eq_getElem?_getD, getD_enumList]

/-- The enumeration of a finset, as an equivalence. -/
noncomputable def enumEquiv (s : Finset α) : Fin s.card ≃ s :=
  Equiv.ofBijective (fun i => ⟨enumGet s i, enumGet_mem s i⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun i j h => enumGet_injective s (congr_arg Subtype.val h), by simp⟩)

@[simp] lemma enumEquiv_apply (s : Finset α) (i : Fin s.card) :
    (enumEquiv s i : α) = enumGet s i := rfl

end enum

/-- Cramer's rule: the solution of an invertible linear system. -/
lemma updateCol_det_div_det {m : ℕ} (A : Matrix (Fin m) (Fin m) ℚ) (hA : A.det ≠ 0)
    {x b : Fin m → ℚ} (h : A *ᵥ x = b) (i : Fin m) : (A.updateCol i b).det / A.det = x i := by
  have hc : A.cramer b = A.det • x := by
    have hinj := (Matrix.mulVec_injective_iff_isUnit (A := A)).2
      ((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hA))
    apply hinj
    rw [mulVec_cramer, Matrix.mulVec_smul, h]
  rw [← cramer_apply, hc, Pi.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hA]

variable {n : ℕ}

/-- The matrix `Mat(C, Ada(C))` built from enumerations `lC`, `lA` of `C` and `Ada(C)`. -/
def matOfLists (m : ℕ) (lC lA : List (Fin n → Fin 3)) : Matrix (Fin m) (Fin m) ℚ :=
  Matrix.of fun i j => matCoef ctmat3 (lC.getD i 0) (lA.getD j 0)

/-- The transpose of `a` (read as a matrix) with its `i`-th column replaced by `b`. -/
def cramerArr (m : ℕ) (a : Array (Array ℚ)) (b : Array ℚ) (i : Fin m) : Array (Array ℚ) :=
  toArr (Matrix.of fun r c : Fin m => if c = i then b.getD r 0 else arrGet a c r)

/-- Solves the system `x · Mat(C, Ada(C)) = t` by Cramer's rule. The `i`-th entry of the result
is the count of the `i`-th element of `enumList C`. -/
def solveArr (C : Finset (Fin n → Fin 3)) (t : (Fin n → Fin 3) → ℚ) : Array ℚ :=
  let lC := enumList C
  let lA := enumList (adapt C)
  let m := C.card
  let a := toArr (matOfLists m lC lA)
  let b : Array ℚ := Array.ofFn fun j : Fin m => t (lA.getD j 0)
  let d := detArr m a
  Array.ofFn fun i : Fin m => detArr m (cramerArr m a b i) / d

/-- The solution of the system for a given candidate sign condition. -/
def solveExec (C : Finset (Fin n → Fin 3)) (t : (Fin n → Fin 3) → ℚ) (σ : Fin n → Fin 3) : ℚ :=
  (solveArr C t).getD ((enumList C).idxOf σ) 0

/-- The executable sign determination algorithm. -/
def signDetExec : ∀ {n : ℕ}, ((Fin n → Fin 3) → ℚ) → Finset (Fin n → Fin 3)
  | 0, oracle => univ.filter fun σ => oracle σ ≠ 0
  | _ + 1, oracle =>
    let C := candidates (signDetExec fun α => oracle (ext 0 α))
    let x := solveArr C oracle
    let lC := enumList C
    (lC.filter fun σ => x.getD (lC.idxOf σ) 0 ≠ 0).toFinset

/-- The counts computed by the executable sign determination algorithm. -/
def countDetExec : ∀ {n : ℕ}, ((Fin n → Fin 3) → ℚ) → (Fin n → Fin 3) → ℚ
  | 0, oracle => oracle
  | _ + 1, oracle => solveExec (candidates (signDetExec fun α => oracle (ext 0 α))) oracle

/-- The executable solver computes the same counts as `Adamar.solveCounts`. -/
theorem solveExec_eq (C : Finset (Fin n → Fin 3)) (t : (Fin n → Fin 3) → ℚ) :
    solveExec C t = solveCounts C t := by
  ext σ
  by_cases hσ : σ ∈ C
  swap
  · -- Outside of `C`, both are zero.
    have hlen : (enumList C).idxOf σ = C.card := by
      rw [← length_enumList, List.idxOf_eq_length_iff, mem_enumList]
      exact hσ
    rw [solveExec, hlen]
    simp [solveArr, solveCounts, hσ, Array.getD_eq_getD_getElem?]
  -- The enumerations of `C` and `Ada(C)`.
  set e : Fin C.card ≃ C := enumEquiv C
  set f : Fin C.card ≃ adapt C := (finCongr (card_adapt C).symm).trans (enumEquiv (adapt C))
  have he : ∀ i : Fin C.card, ((enumList C)[(i : ℕ)]?).getD 0 = (e i : Fin n → Fin 3) :=
    fun i => getElem?_getD_enumList C 0 i
  have hf : ∀ j : Fin C.card, ((enumList (adapt C))[(j : ℕ)]?).getD 0 = (f j : Fin n → Fin 3) :=
    fun j => getElem?_getD_enumList (adapt C) 0 (finCongr (card_adapt C).symm j)
  -- The enumerated matrix is `Mat(C, Ada(C))` with rows and columns reindexed.
  set A := matOfLists C.card (enumList C) (enumList (adapt C))
  have hA : A = (mat ctmat3 C (adapt C)).submatrix e f := by
    ext i j
    simp [A, matOfLists, mat, he, hf, List.getD_eq_getElem?_getD]
  have hAdet : Aᵀ.det ≠ 0 := by
    rw [det_transpose, ← rowFree_iff_det_ne_zero, hA,
      show (mat ctmat3 C (adapt C)).submatrix e f =
        ((mat ctmat3 C (adapt C)).submatrix e id).submatrix id f from rfl,
      rowFree_submatrix_col_equiv_iff, rowFree_submatrix_equiv_iff]
    exact (ctmat_adapted C).2
  -- The counts given by `solveCounts` solve the enumerated system.
  set y : C → ℚ := Matrix.vecMul (fun α : adapt C => t α) (adaptInv C)
  have hy : Matrix.vecMul y (mat ctmat3 C (adapt C)) = fun α : adapt C => t α := by
    rw [Matrix.vecMul_vecMul, adaptInv_mul_mat, Matrix.vecMul_one]
  have hsys : Aᵀ *ᵥ (fun i => y (e i)) = fun j => t (f j) := by
    rw [mulVec_transpose, hA]
    ext j
    have := congr_fun hy (f j)
    simp only [Matrix.vecMul, dotProduct, submatrix_apply] at this ⊢
    rw [← this]
    exact Equiv.sum_comp e (fun σ => y σ * mat ctmat3 C (adapt C) σ (f j))
  -- The index of `σ` in the enumeration of `C`.
  have hidx : (enumList C).idxOf σ < C.card := by
    rw [← length_enumList, List.idxOf_lt_length_iff, mem_enumList]
    exact hσ
  set i : Fin C.card := ⟨_, hidx⟩
  have hei : (e i : Fin n → Fin 3) = σ := by
    simp only [e, enumEquiv_apply, enumGet, i, List.get_eq_getElem, Fin.val_cast]
    exact List.getElem_idxOf _
  have hmat : (Matrix.of fun i j : Fin C.card => arrGet (toArr A) i j) = A := by
    ext
    simp
  have hcr : (Matrix.of fun r c : Fin C.card =>
      arrGet (cramerArr C.card (toArr A) (Array.ofFn fun j : Fin C.card =>
        t ((enumList (adapt C)).getD j 0)) i) r c) = Aᵀ.updateCol i (fun j => t (f j)) := by
    ext r c
    simp [cramerArr, updateCol_apply, hf, Array.getD, List.getD_eq_getElem?_getD]
  rw [solveExec, solveArr]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left_of_eq_true (eq_true (by simpa using hidx)),
    Option.getD_some, detArr_eq_detGE, detArr_eq_detGE, hmat, hcr, detGE_eq_det,
    detGE_eq_det, ← det_transpose A, updateCol_det_div_det _ hAdet hsys, ← hei]
  simp only [solveCounts, y, Matrix.vecMul, dotProduct, e, enumEquiv_apply]
  have h := enumGet_mem C i
  have he' : enumEquiv C i = ⟨enumGet C i, h⟩ := Subtype.ext rfl
  simp [h, he']

theorem signDetExec_eq_countDetExec_eq {oracle : (Fin n → Fin 3) → ℚ} :
    signDetExec oracle = signDet oracle ∧ countDetExec oracle = countDet oracle := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have h1 := (ih (oracle := fun α => oracle (ext 0 α))).1
    refine ⟨?_, ?_⟩
    · show (List.filter _ (enumList _)).toFinset = _
      rw [h1, signDet_succ]
      ext σ
      have := congr_fun (solveExec_eq (candidates (signDet fun α => oracle (ext 0 α))) oracle) σ
      simp only [solveExec, Array.getD_eq_getD_getElem?] at this
      simp [this]
    · show solveExec _ _ = _
      rw [h1, solveExec_eq]
      rfl

/-- The executable algorithm computes the same set as `Adamar.signDet`, for every black box. -/
theorem signDetExec_eq (oracle : (Fin n → Fin 3) → ℚ) : signDetExec oracle = signDet oracle :=
  signDetExec_eq_countDetExec_eq.1

/-- The executable algorithm computes the same counts as `Adamar.countDet`. -/
theorem countDetExec_eq (oracle : (Fin n → Fin 3) → ℚ) :
    countDetExec oracle = countDet oracle :=
  signDetExec_eq_countDetExec_eq.2

/-- **Correctness of the executable sign determination algorithm.** -/
theorem signDetExec_correct {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {P : Type*} (Z : Finset P) (Q : Fin n → P → R) (oracle : (Fin n → Fin 3) → ℚ)
    (h : OracleCorrect Z Q (Nat.log 2 Z.card + 1) oracle) :
    signDetExec oracle = SIGN Z Q ∧ ∀ σ, countDetExec oracle σ = cnt Z Q σ := by
  obtain ⟨h1, h2, -⟩ := signDet_correct Z Q oracle h
  exact ⟨(signDetExec_eq oracle).trans h1, fun σ => by rw [countDetExec_eq, h2]⟩

/-- Correctness of the executable algorithm when the black box is correct on the queries
actually made (see `Adamar.signDet_correct_of_queries`). -/
theorem signDetExec_correct_of_queries {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] {P : Type*} (Z : Finset P) (Q : Fin n → P → R)
    (oracle : (Fin n → Fin 3) → ℚ) (h : ∀ α ∈ queries oracle, oracle α = TaQ Z (qpow Q α)) :
    signDetExec oracle = SIGN Z Q ∧ ∀ σ, countDetExec oracle σ = cnt Z Q σ := by
  obtain ⟨h1, h2, -⟩ := signDet_correct_of_queries Z Q oracle h
  exact ⟨(signDetExec_eq oracle).trans h1, fun σ => by rw [countDetExec_eq, h2]⟩

end Adamar
