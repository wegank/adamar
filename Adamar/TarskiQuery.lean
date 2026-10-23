/-
Copyright (c) 2026 Weijia Wang. All rights reserved.
-/
import Adamar.Signdet3

/-!
# Tarski queries and sign determination

This file is *not* part of the Coq development `signdet.v`: it formalizes the setting of
Sections 1 and 2 of the accompanying paper (Cohen, *Formalization of a sign determination
algorithm in real algebraic geometry*), i.e. Section 10.3 of *Algorithms in Real Algebraic
Geometry* (Basu, Pollack, Roy), and connects it to the adapted families of `Adamar.Adapt`.

Let `R` be an ordered field, `Z` a finite set of points and `Q = (Q₀, …, Q_{s-1})` a family of
functions on the points (e.g. polynomials evaluated at the points). We define

* `Adamar.signCond Q z : Fin s → Fin 3`: the sign condition realized by `Q` at `z`, where the
  signs `0, 1, -1` are encoded by `0, 1, 2 : Fin 3` (see `Adamar.signIdx`);
* `Adamar.SIGN Z Q`: the set of sign conditions realized by `Q` on `Z`;
* `Adamar.cnt Z Q σ`: the number `c(σ, Z)` of points of `Z` realizing `σ`;
* `Adamar.TaQ Z f = ∑_{z ∈ Z} sign (f z)`: the Tarski query of `f` on `Z`;
* `Adamar.qpow Q α = ∏ i, Q i ^ α i`: the product `Q^α` for `α : Fin s → Fin 3`.

## Main results

* `Adamar.TaQ_qpow_eq_sum` (book: Prop. 10.70): if `SIGN Z Q ⊆ S`, then for every `α`,
  `TaQ Z (Q^α) = ∑_{σ ∈ S} c(σ, Z) σ^α`, i.e. `TaQ(Q^A, Z) = c(S, Z) · Mat(S, A)`.
* `Adamar.cnt_eq_sum_TaQ`: for every `S ⊇ SIGN Z Q`, the counts `c(σ, Z)` are given by a
  fixed linear combination (depending only on `S`) of the Tarski queries `TaQ(Q^α, Z)` for
  `α ∈ adapt S`.
* `Adamar.sign_determination`: the "better sign determination" statement, gathering the
  above with `#adapt S = #S` and the bound `log₂ #S` on the number of factors of each
  product `Q^α`. For `S = SIGN(Q, Z)`, this bound is at most `log₂ #Z`
  (`Adamar.card_support_le_log_card`).
* `Adamar.sign_determination_roots`: the univariate polynomial instance, where `Z` is the
  set of roots of a polynomial `P`, so that `#S ≤ deg P`.
-/

namespace Adamar

open Finset

section inverse

variable {F : Type*} [Field F]

/-- Permuting the columns of a matrix does not change row-freeness. -/
lemma rowFree_submatrix_col_equiv_iff {m n n' : Type*} (A : Matrix m n F) (e : n' ≃ n) :
    RowFree (A.submatrix id e) ↔ RowFree A := by
  let f : (n → F) ≃ₗ[F] (n' → F) := LinearEquiv.funCongrLeft F F e
  have : (A.submatrix id e).row = f ∘ A.row := by
    ext i j
    rfl
  rw [RowFree, RowFree, this]
  exact LinearMap.linearIndependent_iff f.toLinearMap f.ker

/-- A row-free matrix with as many rows as columns has a two-sided inverse. -/
lemma exists_inverse_of_rowFree {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n F) (hc : Fintype.card m = Fintype.card n)
    (hA : RowFree A) : ∃ B : Matrix n m F, A * B = 1 ∧ B * A = 1 := by
  let e : m ≃ n := Fintype.equivOfCardEq hc
  set A' : Matrix m m F := A.submatrix id e
  have hA' : IsUnit A'.det :=
    (Matrix.isUnit_iff_isUnit_det A').1 ((rowFree_iff_isUnit A').1
      ((rowFree_submatrix_col_equiv_iff A e).2 hA))
  have hAA' : A = A'.submatrix id e.symm := by
    ext i j
    simp [A']
  refine ⟨A'⁻¹.submatrix e.symm id, ?_, ?_⟩
  · rw [hAA', Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ hA', Matrix.submatrix_id_id]
  · rw [hAA']
    change A'⁻¹.submatrix e.symm (Equiv.refl m) * A'.submatrix (Equiv.refl m) e.symm = 1
    rw [Matrix.submatrix_mul_equiv, Matrix.nonsing_inv_mul _ hA', Matrix.submatrix_one_equiv]

end inverse

section signs

/-- The encoding of the signs `0, 1, -1` as `0, 1, 2 : Fin 3`, inverse to `Adamar.sign`. -/
def signIdx : SignType → Fin 3
  | .zero => 0
  | .pos => 1
  | .neg => 2

@[simp] lemma sign_signIdx (t : SignType) : Adamar.sign (signIdx t) = (t : ℚ) := by
  cases t <;> simp [signIdx]

lemma signIdx_injective : Function.Injective signIdx := by
  intro a b h
  cases a <;> cases b <;> simp_all [signIdx]

variable {R : Type*} [Field R] [LinearOrder R]
variable {P : Type*} {s : ℕ}

/-- The sign condition realized by the family `Q` at the point `z`. -/
def signCond (Q : Fin s → P → R) (z : P) : Fin s → Fin 3 :=
  fun i => signIdx (SignType.sign (Q i z))

/-- The set `SIGN(Q, Z)` of sign conditions realized by `Q` on `Z`. -/
def SIGN (Z : Finset P) (Q : Fin s → P → R) : Finset (Fin s → Fin 3) :=
  Z.image (signCond Q)

/-- The number `c(σ, Z)` of points of `Z` at which `Q` realizes the sign condition `σ`. -/
def cnt (Z : Finset P) (Q : Fin s → P → R) (σ : Fin s → Fin 3) : ℕ :=
  #{z ∈ Z | signCond Q z = σ}

/-- The Tarski query `TaQ(f, Z) = ∑_{z ∈ Z} sign (f z)`. -/
def TaQ (Z : Finset P) (f : P → R) : ℤ := ∑ z ∈ Z, (SignType.sign (f z) : ℤ)

/-- The product `Q^α = ∏ i, (Q i) ^ (α i)`. -/
def qpow (Q : Fin s → P → R) (α : Fin s → Fin 3) : P → R :=
  fun z => ∏ i, Q i z ^ (α i : ℕ)

variable (Z : Finset P) (Q : Fin s → P → R)

lemma mem_SIGN {σ : Fin s → Fin 3} : σ ∈ SIGN Z Q ↔ ∃ z ∈ Z, signCond Q z = σ := by
  simp [SIGN]

lemma card_SIGN_le : (SIGN Z Q).card ≤ Z.card := card_image_le

/-- A sign condition is realized iff it is realized by a positive number of points. -/
lemma cnt_pos_iff {σ : Fin s → Fin 3} : 0 < cnt Z Q σ ↔ σ ∈ SIGN Z Q := by
  simp [cnt, card_pos, Finset.Nonempty, mem_SIGN]

lemma cnt_eq_zero_iff {σ : Fin s → Fin 3} : cnt Z Q σ = 0 ↔ σ ∉ SIGN Z Q := by
  rw [← cnt_pos_iff]
  omega

/-- The counts of the sign conditions add up to the number of points. -/
lemma sum_cnt {S : Finset (Fin s → Fin 3)} (hS : SIGN Z Q ⊆ S) :
    ∑ σ ∈ S, cnt Z Q σ = Z.card := by
  rw [card_eq_sum_card_fiberwise (f := signCond Q) fun z hz => hS (mem_image_of_mem _ hz)]
  rfl

/-- The Tarski query of `1` counts the points. -/
lemma TaQ_one [IsStrictOrderedRing R] : TaQ Z (fun _ => (1 : R)) = Z.card := by
  simp [TaQ]

/-- The sign of `Q^α` at `z` is the coefficient of `ctmat3`'s tensor power indexed by the sign
condition realized at `z` and `α`. -/
lemma sign_qpow [IsStrictOrderedRing R] (α : Fin s → Fin 3) (z : P) :
    ((SignType.sign (qpow Q α z) : ℤ) : ℚ) = matCoef ctmat3 (signCond Q z) α := by
  have h1 : SignType.sign (qpow Q α z) = ∏ i, SignType.sign (Q i z) ^ (α i : ℕ) := by
    simp only [qpow]
    rw [← signHom_apply, map_prod]
    simp [sign_pow]
  rw [h1, matCoef, SignType.intCast_cast]
  simp only [signCond, ctmat3, Matrix.of_apply, sign_signIdx]
  have := map_prod (SignType.castHom (α := ℚ))
    (fun i => SignType.sign (Q i z) ^ (α i : ℕ)) univ
  simp only [map_pow] at this
  exact this

/-- **Proposition 10.70** of the book: if `SIGN(Q, Z) ⊆ S`, the Tarski queries of the
products `Q^α` are obtained from the counts by the matrix of signs. -/
theorem TaQ_qpow_eq_sum [IsStrictOrderedRing R] {S : Finset (Fin s → Fin 3)}
    (hS : SIGN Z Q ⊆ S)
    (α : Fin s → Fin 3) :
    (TaQ Z (qpow Q α) : ℚ) = ∑ σ ∈ S, (cnt Z Q σ : ℚ) * matCoef ctmat3 σ α := by
  rw [TaQ, Int.cast_sum]
  simp_rw [sign_qpow]
  rw [← sum_fiberwise_of_maps_to (g := signCond Q) fun z hz => hS (mem_image_of_mem _ hz)]
  refine sum_congr rfl fun σ _ => ?_
  rw [sum_congr rfl fun z hz => by rw [(mem_filter.1 hz).2], sum_const, nsmul_eq_mul]
  rfl

/-- Matrix form of Proposition 10.70: `TaQ(Q^A, Z) = c(S, Z) · Mat(S, A)`. -/
theorem TaQ_qpow_eq_vecMul [IsStrictOrderedRing R] {S : Finset (Fin s → Fin 3)}
    (hS : SIGN Z Q ⊆ S)
    (A : Finset (Fin s → Fin 3)) :
    (fun α : A => (TaQ Z (qpow Q α) : ℚ)) =
      Matrix.vecMul (fun σ : S => (cnt Z Q σ : ℚ)) (mat ctmat3 S A) := by
  ext α
  rw [TaQ_qpow_eq_sum Z Q hS, ← sum_coe_sort S]
  rfl

end signs

section determination

variable {n : ℕ}

/-- The inverse of the (invertible) matrix `Mat(S, Ada(S))`. -/
noncomputable def adaptInv (S : Finset (Fin n → Fin 3)) : Matrix (adapt S) S ℚ :=
  (exists_inverse_of_rowFree (mat ctmat3 S (adapt S))
    (by simp [Fintype.card_coe]) (ctmat_adapted S).2).choose

lemma mat_mul_adaptInv (S : Finset (Fin n → Fin 3)) :
    mat ctmat3 S (adapt S) * adaptInv S = 1 :=
  (exists_inverse_of_rowFree (mat ctmat3 S (adapt S))
    (by simp [Fintype.card_coe]) (ctmat_adapted S).2).choose_spec.1

lemma adaptInv_mul_mat (S : Finset (Fin n → Fin 3)) :
    adaptInv S * mat ctmat3 S (adapt S) = 1 :=
  (exists_inverse_of_rowFree (mat ctmat3 S (adapt S))
    (by simp [Fintype.card_coe]) (ctmat_adapted S).2).choose_spec.2

variable {R : Type*} [Field R] [LinearOrder R]
variable {P : Type*} (Z : Finset P) (Q : Fin n → P → R)

/-- The counts `c(σ, Z)`, for `σ ∈ S ⊇ SIGN(Q, Z)`, are a fixed linear combination
(depending only on `S`) of the Tarski queries `TaQ(Q^α, Z)`, for `α ∈ Ada(S)`. -/
theorem cnt_eq_sum_TaQ [IsStrictOrderedRing R] {S : Finset (Fin n → Fin 3)}
    (hS : SIGN Z Q ⊆ S) (σ : S) :
    (cnt Z Q σ : ℚ) = ∑ α : adapt S, (TaQ Z (qpow Q α) : ℚ) * adaptInv S α σ := by
  have h := congr_arg (fun t => Matrix.vecMul t (adaptInv S)) (TaQ_qpow_eq_vecMul Z Q hS (adapt S))
  simp only [Matrix.vecMul_vecMul, mat_mul_adaptInv, Matrix.vecMul_one] at h
  exact (congr_fun h σ).symm

/-- Two configurations whose realized sign conditions lie in `S` and with the same Tarski
queries on `Ada(S)` have the same counts for all sign conditions. -/
theorem cnt_eq_of_TaQ_eq [IsStrictOrderedRing R] {P' R' : Type*} [Field R'] [LinearOrder R']
    [IsStrictOrderedRing R']
    (Z' : Finset P') (Q' : Fin n → P' → R') {S : Finset (Fin n → Fin 3)}
    (hS : SIGN Z Q ⊆ S) (hS' : SIGN Z' Q' ⊆ S)
    (hT : ∀ α ∈ adapt S, TaQ Z (qpow Q α) = TaQ Z' (qpow Q' α)) (σ : Fin n → Fin 3) :
    cnt Z Q σ = cnt Z' Q' σ := by
  by_cases hσ : σ ∈ S
  · have h := cnt_eq_sum_TaQ Z Q hS ⟨σ, hσ⟩
    rw [sum_congr rfl fun α _ => by rw [hT α α.2], ← cnt_eq_sum_TaQ Z' Q' hS' ⟨σ, hσ⟩]
      at h
    exact_mod_cast h
  · rw [(cnt_eq_zero_iff Z Q).2 (fun h => hσ (hS h)),
      (cnt_eq_zero_iff Z' Q').2 (fun h => hσ (hS' h))]

/-- **Better sign determination.** Let `S ⊇ SIGN(Q, Z)` be a set of candidate sign
conditions. Then
1. the family `Ada(S)` has `#S` elements;
2. each `α ∈ Ada(S)` has at most `log₂ #S` non-zero entries, i.e. `Q^α` is a product of at
   most `log₂ #S` of the `Q i` or `Q i ^ 2`;
3. the counts `c(σ, Z)` for `σ ∈ S` are computed from the `#S` Tarski queries `TaQ(Q^α, Z)`,
   `α ∈ Ada(S)`, by the inverse of `Mat(S, Ada(S))`; and
4. the realized sign conditions are those with a non-zero count. -/
theorem sign_determination [IsStrictOrderedRing R] {S : Finset (Fin n → Fin 3)}
    (hS : SIGN Z Q ⊆ S) :
    (adapt S).card = S.card ∧
    (∀ α ∈ adapt S, #{i | α i ≠ 0} ≤ Nat.log 2 S.card) ∧
    (∀ σ : S,
      (cnt Z Q σ : ℚ) = ∑ α : adapt S, (TaQ Z (qpow Q α) : ℚ) * adaptInv S α σ) ∧
    SIGN Z Q = {σ ∈ S | cnt Z Q σ ≠ 0} :=
  ⟨card_adapt S, fun α hα => prop_10_84 S α hα, cnt_eq_sum_TaQ Z Q hS, by
    ext σ
    simp only [mem_filter, ne_eq, cnt_eq_zero_iff, not_not]
    exact ⟨fun h => ⟨hS h, h⟩, fun h => h.2⟩⟩

/-- When `S = SIGN(Q, Z)` is exactly the set of realized sign conditions, the products `Q^α`
used for sign determination involve at most `log₂ #Z` polynomials. -/
theorem card_support_le_log_card {α : Fin n → Fin 3} (hα : α ∈ adapt (SIGN Z Q)) :
    #{i | α i ≠ 0} ≤ Nat.log 2 Z.card :=
  (prop_10_84 _ α hα).trans (Nat.log_mono_right (card_SIGN_le Z Q))

end determination

section polynomial

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] {n : ℕ}

/-- The univariate Tarski query `TaQ(Q, P) = ∑_{x, P(x) = 0} sign (Q x)`. -/
noncomputable def TaQPoly (P Q : R[X]) : ℤ := TaQ P.roots.toFinset fun x => Q.eval x

/-- The products `Q^α` of a family of polynomials. -/
noncomputable def polyPow (Q : Fin n → R[X]) (α : Fin n → Fin 3) : R[X] :=
  ∏ i, Q i ^ (α i : ℕ)

lemma TaQPoly_polyPow (P : R[X]) (Q : Fin n → R[X]) (α : Fin n → Fin 3) :
    TaQPoly P (polyPow Q α) = TaQ P.roots.toFinset (qpow (fun i x => (Q i).eval x) α) := by
  simp only [TaQPoly, polyPow, eval_prod, eval_pow]
  rfl

/-- **Better sign determination for the roots of a univariate polynomial.** Let `P` and
`Q₀, …, Q_{n-1}` be polynomials (if `P = 0`, Mathlib's convention `roots 0 = 0` makes the
statement trivial), and let `S = SIGN(Q, Zer(P))`. Then `#S ≤ deg P`, and the
numbers of roots of `P` realizing each sign condition `σ ∈ S` are given by the `#S`
univariate Tarski queries `TaQ(Q^α, P)`, `α ∈ Ada(S)`, each of which involves a product of at
most `log₂ (deg P)` of the polynomials `Q i` or `Q i ^ 2`. -/
theorem sign_determination_roots [IsStrictOrderedRing R] {P : R[X]} (Q : Fin n → R[X]) :
    let Z := P.roots.toFinset
    let S := SIGN Z fun i x => (Q i).eval x
    S.card ≤ P.natDegree ∧ (adapt S).card = S.card ∧
    (∀ α ∈ adapt S, #{i | α i ≠ 0} ≤ Nat.log 2 P.natDegree) ∧
    ∀ σ : S, (cnt Z (fun i x => (Q i).eval x) σ : ℚ) =
      ∑ α : adapt S, (TaQPoly P (polyPow Q α) : ℚ) * adaptInv S α σ := by
  intro Z S
  have hZ : Z.card ≤ P.natDegree := (Multiset.toFinset_card_le _).trans (card_roots' P)
  refine ⟨(card_SIGN_le _ _).trans hZ, card_adapt S, fun α hα => ?_, fun σ => ?_⟩
  · exact (card_support_le_log_card Z _ hα).trans (Nat.log_mono_right hZ)
  · simp_rw [TaQPoly_polyPow]
    exact cnt_eq_sum_TaQ Z _ subset_rfl σ

end polynomial

end Adamar
