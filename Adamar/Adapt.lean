/-
Copyright (c) 2026 Weijia Wang. All rights reserved.
Portions copyright (c) 2014 Cyril Cohen (Coq development `signdet.v`), used under the MIT
license as described in the file LICENSE.
-/
import Adamar.Ext

/-!
# Adapted families for an abstract square matrix

This file is the Lean counterpart of the section `AbstractSigndet` of `signdet.v`.

We fix a field `F`, a positive integer `k` and a square matrix `M` of size `k`, whose rows and
columns are indexed by `X = Fin k`. For sets `S, A` of tuples in `X ^ n`, the matrix
`mat M S A` is the submatrix of the `n`-fold tensor power of `M` with rows in `S` and columns
in `A`.

The main definition is the adapted family `adapt S` (book: `Ada(Σ)`, Definition 10.77),
defined recursively as the disjoint union of the sets `i · adapt (Ξᵢ S)` for `i < k`.

## Main results

* `Adamar.mat_adapt_free`: if every leftmost square submatrix of `M` (with any choice of rows)
  is invertible, the rows of `mat M S (adapt S)` are linearly independent (book: Prop. 10.82).
* `Adamar.card_adapt`: `#(adapt S) = #S`.
* `Adamar.adapt_adapted`: hence `mat M S (adapt S)` is invertible.
* `Adamar.adapt_mono`: `adapt` is monotone (book: Lemma 10.78).
* `Adamar.adapt_down_closed`: `adapt S` is downward closed (book: Lemma 10.85).
* `Adamar.prop_10_84`: every `a ∈ adapt S` has at most `log₂ #S` non-zero entries
  (book: Prop. 10.84).
-/

namespace Adamar

open Finset

section RowFree

variable {F : Type*} [Field F]

/-- A matrix is *row-free* when its rows are linearly independent (Coq: `row_free`).
For a square matrix this is equivalent to invertibility, see `Adamar.rowFree_iff_isUnit`. -/
def RowFree {m n : Type*} (A : Matrix m n F) : Prop := LinearIndependent F A.row

lemma rowFree_iff_sum {m n : Type*} [Fintype m] (A : Matrix m n F) :
    RowFree A ↔ ∀ g : m → F, (∀ j, ∑ i, g i * A i j = 0) → ∀ i, g i = 0 := by
  rw [RowFree, Fintype.linearIndependent_iff]
  refine forall_congr' fun g => imp_congr_left ?_
  rw [funext_iff]
  simp [Finset.sum_apply, Matrix.row]

lemma rowFree_iff_isUnit {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m F) :
    RowFree A ↔ IsUnit A :=
  Matrix.linearIndependent_row_iff_isUnit

lemma rowFree_iff_det_ne_zero {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m F) :
    RowFree A ↔ A.det ≠ 0 := by
  rw [rowFree_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- Row-freeness of a matrix whose rows are indexed by a finset `S`, expressed with finset sums
over `S` and a coefficient function defined on the whole ambient type. -/
lemma rowFree_finset_iff {ι n : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → n → F) :
    RowFree (Matrix.of fun (i : S) (j : n) => f i j) ↔
      ∀ l : ι → F, (∀ j, ∑ s ∈ S, l s * f s j = 0) → ∀ s ∈ S, l s = 0 := by
  rw [rowFree_iff_sum]
  constructor
  · intro h l hl s hs
    refine h (fun i => l i) (fun j => ?_) ⟨s, hs⟩
    rw [← hl j, ← sum_coe_sort S]
    rfl
  · intro h g hg i
    have := h (fun s => if hs : s ∈ S then g ⟨s, hs⟩ else 0) (fun j => ?_) i i.2
    · simpa using this
    · rw [← sum_coe_sort S, ← hg j]
      refine sum_congr rfl fun s _ => ?_
      simp

end RowFree

variable {F : Type*} [Field F] {k : ℕ}

section adapt

/-- The adapted family (book: `Ada(Σ)`, Definition 10.77). It is defined by recursion on the
length `n` of the tuples, as the union of `extset i (adapt (Xi i S))` for `i < k`. -/
def adapt : ∀ {n : ℕ}, Finset (Fin n → Fin k) → Finset (Fin n → Fin k)
  | 0, S => S
  | _ + 1, S => univ.biUnion fun i : Fin k => extset i (adapt (Xi i S))

variable {n : ℕ}

@[simp] lemma adapt_zero (S : Finset (Fin 0 → Fin k)) : adapt S = S := rfl

lemma adapt_succ (S : Finset (Fin (n + 1) → Fin k)) :
    adapt S = univ.biUnion fun i : Fin k => extset i (adapt (Xi i S)) := rfl

/-- Coq: `adaptn0`. -/
@[simp] lemma adapt_empty : adapt (∅ : Finset (Fin n → Fin k)) = ∅ := by
  induction n with
  | zero => rfl
  | succ n ih => ext; simp [adapt_succ, ih]

/-- Coq: `in_adapt`. -/
lemma mem_adapt (S : Finset (Fin (n + 1) → Fin k)) (a : Fin (n + 1) → Fin k) :
    a ∈ adapt S ↔ rem a ∈ adapt (Xi (a 0) S) := by
  simp [adapt_succ, mem_extset]

/-- `adapt` is monotone (Coq: `subset_adapt`, book: Lemma 10.78). -/
lemma adapt_mono {S S' : Finset (Fin n → Fin k)} (h : S ⊆ S') : adapt S ⊆ adapt S' := by
  induction n with
  | zero => exact h
  | succ n ih =>
    intro a ha
    rw [mem_adapt] at ha ⊢
    exact ih (Xi_mono _ h) ha

lemma ext_mem_adapt {S : Finset (Fin (n + 1) → Fin k)} {x : Fin k} {b : Fin n → Fin k} :
    ext x b ∈ adapt S ↔ b ∈ adapt (Xi x S) := by
  simp [mem_adapt]

/-- Coq: `adapt_eq0`. -/
@[simp] lemma adapt_eq_empty [NeZero k] {S : Finset (Fin n → Fin k)} :
    adapt S = ∅ ↔ S = ∅ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine ⟨fun h => ?_, fun h => h ▸ adapt_empty⟩
    by_contra hS
    have h0 : Xi 0 S ≠ ∅ := fun h0 => hS (Xi_zero_eq_empty.1 h0)
    obtain ⟨b, hb⟩ := nonempty_iff_ne_empty.2 (mt ih.1 h0)
    have : ext 0 b ∈ adapt S := ext_mem_adapt.2 (by simpa using hb)
    simp [h] at this

/-- `adapt S` is downward closed (Coq: `adapt_down_closed`, book: Lemma 10.85). -/
lemma adapt_down_closed {S : Finset (Fin n → Fin k)} {a b : Fin n → Fin k}
    (hba : ∀ i, b i ≤ a i) (ha : a ∈ adapt S) : b ∈ adapt S := by
  induction n with
  | zero => exact Subsingleton.elim a b ▸ ha
  | succ n ih =>
    rw [mem_adapt] at ha ⊢
    have : rem b ∈ adapt (Xi (a 0) S) := ih (fun i => hba i.succ) ha
    exact adapt_mono (Xi_anti S (by simpa using hba 0)) this

/-- Coq: `card_adapt`. -/
@[simp] lemma card_adapt (S : Finset (Fin n → Fin k)) : (adapt S).card = S.card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [adapt_succ, card_biUnion]
    · simp only [card_extset, ih]
      rw [Fin.sum_univ_eq_sum_range (fun m => (Xi m S).card), ← sum_card_Xi S,
        Fintype.card_fin]
    · intro i _ j _ hij
      exact disjoint_extset hij _ _

end adapt

section matrix

variable (M : Matrix (Fin k) (Fin k) F)

/-- The leftmost square submatrix of `M` with rows in `S`, i.e. the submatrix of `M` with rows
in `S` and the `#S` first columns. -/
def mat1 (S : Finset (Fin k)) : Matrix S (Fin S.card) F :=
  Matrix.of fun i j => M i (Fin.castLE (by simpa using card_le_univ S) j)

/-- The coefficients of the `n`-fold tensor power of `M`. -/
def matCoef {n : ℕ} (i j : Fin n → Fin k) : F := ∏ l, M (i l) (j l)

/-- The submatrix of the `n`-fold tensor power of `M` with rows in `S` and columns in `A`
(book: `Mat(A, Σ)`, up to transposition). -/
def mat {n : ℕ} (S A : Finset (Fin n → Fin k)) : Matrix S A F :=
  Matrix.of fun i j => matCoef M i.1 j.1

/-- `A` is adapted to `S` when `mat M S A` is square and invertible. Since the indexing types
of `mat M S A` are not definitionally equal, we state it as an equality of cardinals together
with row-freeness (book: Definition 10.73). -/
def adapted {n : ℕ} (S A : Finset (Fin n → Fin k)) : Prop :=
  A.card = S.card ∧ RowFree (mat M S A)

variable {M} {n : ℕ}

/-- Coq: `mat_coefS`. -/
lemma matCoef_succ (s a : Fin (n + 1) → Fin k) :
    matCoef M s a = M (s 0) (a 0) * matCoef M (rem s) (rem a) :=
  Fin.prod_univ_succ _

@[simp] lemma matCoef_zero (s a : Fin 0 → Fin k) : matCoef M s a = 1 :=
  Fin.prod_univ_zero _

lemma rowFree_mat_iff (S A : Finset (Fin n → Fin k)) :
    RowFree (mat M S A) ↔
      ∀ l : (Fin n → Fin k) → F, (∀ a ∈ A, ∑ s ∈ S, l s * matCoef M s a = 0) →
        ∀ s ∈ S, l s = 0 := by
  rw [mat, rowFree_finset_iff S (fun s (a : A) => matCoef M s a)]
  simp

lemma rowFree_mat1_iff (S : Finset (Fin k)) :
    RowFree (mat1 M S) ↔
      ∀ l : Fin k → F, (∀ j : Fin k, j.val < S.card → ∑ x ∈ S, l x * M x j = 0) →
        ∀ x ∈ S, l x = 0 := by
  rw [mat1, rowFree_finset_iff S (fun x j => M x (Fin.castLE _ j))]
  refine forall_congr' fun l => imp_congr_left ⟨fun h j hj => ?_, fun h j => h _ j.2⟩
  exact h ⟨j, hj⟩

/-- The main theorem: if all the leftmost square submatrices of `M` are invertible, then the
rows of `mat M S (adapt S)` are linearly independent (Coq: `mat_adapt_free`).

The proof is by induction on `n`, and for a fixed `n`, by induction on the number of
completions of the restriction of a row. -/
theorem mat_adapt_free (hM : ∀ S : Finset (Fin k), RowFree (mat1 M S))
    (S : Finset (Fin n → Fin k)) : RowFree (mat M S (adapt S)) := by
  induction n with
  | zero =>
    rw [rowFree_mat_iff]
    intro l hl s hs
    have := hl s hs
    rwa [sum_eq_single_of_mem s hs (fun t _ hts => absurd (Subsingleton.elim t s) hts),
      matCoef_zero, mul_one] at this
  | succ n ihn =>
    rw [rowFree_mat_iff]
    intro l hl
    -- We show that `l t = 0` by induction on the number of completions of `rem t`.
    suffices H : ∀ r : ℕ, ∀ t ∈ S, (completions S (rem t)).card ≤ r → l t = 0 from
      fun t ht => H _ t ht le_rfl
    intro r
    induction r with
    | zero =>
      intro t ht hc
      exact absurd (card_pos.2 (completions_rem_nonempty ht)) (by omega)
    | succ r ihr =>
      intro t ht hc
      rcases Nat.lt_or_eq_of_le hc with hc | hc
      · exact ihr t ht (by omega)
      set u := rem t with hu
      set C := completions S u with hC
      -- It suffices to show that `l (ext x u) = 0` for all completions `x` of `u`.
      suffices key : ∀ x ∈ C, l (ext x u) = 0 by
        simpa [hu] using key (t 0) (zero_mem_completions_rem ht)
      -- We use the invertibility of the leftmost submatrix of `M` with rows in `C`.
      refine (rowFree_mat1_iff C).1 (hM C) (fun x => l (ext x u)) fun j hj => ?_
      have hjr : (j : ℕ) ≤ r := by omega
      set G : (Fin n → Fin k) → F := fun u' => ∑ x ∈ completions S u', l (ext x u') * M x j
        with hG
      show G u = 0
      -- Rows whose restriction has at most `r` completions do not contribute to `G`.
      have hG0 : ∀ u', u' ∉ Xi r S → G u' = 0 := fun u' hu' => by
        refine sum_eq_zero fun x hx => ?_
        rw [ihr (ext x u') (mem_completions.1 hx) (by simpa using hu'), zero_mul]
      -- We use the induction hypothesis on `Xi r S`.
      refine (rowFree_mat_iff _ _).1 (ihn (Xi r S)) G (fun b hb => ?_) u (by simp [C, hc])
      have hjb : ext j b ∈ adapt S := ext_mem_adapt.2 (adapt_mono (Xi_anti S hjr) hb)
      rw [← hl _ hjb, sum_subset (subset_univ _) fun u' _ hu' => by rw [hG0 u' hu', zero_mul],
        sum_eq_sum_completions S]
      refine sum_congr rfl fun u' _ => ?_
      rw [hG, sum_mul]
      refine sum_congr rfl fun x _ => ?_
      rw [matCoef_succ]
      simp [mul_assoc]

/-- Coq: `adapt_adapted` (book: Proposition 10.82). -/
theorem adapt_adapted (hM : ∀ S : Finset (Fin k), RowFree (mat1 M S))
    (S : Finset (Fin n → Fin k)) : adapted M S (adapt S) :=
  ⟨card_adapt S, mat_adapt_free hM S⟩

end matrix

/-- If `a ∈ adapt S` has `m` non-zero entries, the `2 ^ m` tuples obtained by nullifying some
of them are in `adapt S`, hence `2 ^ m ≤ #S`. -/
theorem two_pow_card_support_le [NeZero k] {n : ℕ} (S : Finset (Fin n → Fin k))
    (a : Fin n → Fin k) (ha : a ∈ adapt S) :
    2 ^ (univ.filter fun i => a i ≠ 0).card ≤ S.card := by
  classical
  set I := univ.filter fun i => a i ≠ 0
  -- Nullify the entries of `a` outside of `J`.
  let nullify (J : Finset (Fin n)) : Fin n → Fin k := fun i => if i ∈ J then a i else 0
  calc 2 ^ I.card = I.powerset.card := (card_powerset I).symm
    _ = (I.powerset.image nullify).card := by
        refine (card_image_of_injOn fun J₁ hJ₁ J₂ hJ₂ h => ?_).symm
        simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hJ₁ hJ₂
        have hne : ∀ i ∈ I, a i ≠ 0 := fun i hi => (mem_filter.1 hi).2
        ext i
        have hi := congr_fun h i
        simp only [nullify] at hi
        constructor
        · intro hi₁
          by_contra hi₂
          simp [hi₁, hi₂, hne i (hJ₁ hi₁)] at hi
        · intro hi₂
          by_contra hi₁
          simp only [hi₁, hi₂, ite_false, ite_true] at hi
          exact hne i (hJ₂ hi₂) hi.symm
    _ ≤ (adapt S).card := by
        refine card_le_card fun b hb => ?_
        obtain ⟨J, -, rfl⟩ := mem_image.1 hb
        refine adapt_down_closed (fun i => ?_) ha
        simp only [nullify]
        split_ifs
        · exact le_rfl
        · exact Fin.zero_le _
    _ = S.card := card_adapt S

/-- Every element of the adapted family has at most `log₂ #S` non-zero entries
(Coq: `prop_10_84`, book: Proposition 10.84). -/
theorem prop_10_84 [NeZero k] {n : ℕ} (S : Finset (Fin n → Fin k)) (a : Fin n → Fin k)
    (ha : a ∈ adapt S) : (univ.filter fun i => a i ≠ 0).card ≤ Nat.log 2 S.card :=
  Nat.le_log_of_pow_le one_lt_two (two_pow_card_support_le S a ha)

/-- Proposition 10.84 as stated in the book: the number of non-zero entries of an element of
`adapt S` is smaller than the bitsize `bit(#S)` of `#S`. -/
theorem prop_10_84_bit [NeZero k] {n : ℕ} (S : Finset (Fin n → Fin k)) (a : Fin n → Fin k)
    (ha : a ∈ adapt S) : (univ.filter fun i => a i ≠ 0).card < Nat.size S.card :=
  Nat.lt_size.2 (two_pow_card_support_le S a ha)

section univ

variable {n : ℕ}

lemma Xi_univ {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ} (hm : m < Fintype.card X) :
    Xi m (univ : Finset (Fin (n + 1) → X)) = univ := by
  ext r
  simp [completions, hm]

/-- The adapted family of the set of all tuples is the set of all tuples. -/
@[simp] lemma adapt_univ : adapt (univ : Finset (Fin n → Fin k)) = univ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext a
    rw [mem_adapt, Xi_univ (by simp), ih]
    simp

/-- **Naive sign determination** (book: Corollary 10.71, Algorithm 10.72): under the
assumption of `Adamar.mat_adapt_free`, the full `k ^ n × k ^ n` tensor power of `M` is
invertible. -/
theorem isUnit_mat_univ {F : Type*} [Field F] {M : Matrix (Fin k) (Fin k) F}
    (hM : ∀ S : Finset (Fin k), RowFree (mat1 M S)) :
    IsUnit (mat M (univ : Finset (Fin n → Fin k)) univ) := by
  rw [← rowFree_iff_isUnit]
  have h := mat_adapt_free hM (univ : Finset (Fin n → Fin k))
  rwa [adapt_univ] at h

end univ

end Adamar
