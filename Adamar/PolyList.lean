/-
Copyright (c) 2026 Weijia Wang. All rights reserved.
-/
import Mathlib

/-!
# Executable polynomials over `ℚ`

Polynomials in Mathlib are not computable. For the executable version of the sign
determination at the roots of a polynomial, we represent a polynomial over `ℚ` by the list of
its coefficients (constant coefficient first), interpreted by `Adamar.PolyL.toPoly`, and we
define the operations needed to compute Sturm sequences: addition, multiplication, derivative
and Euclidean remainder. Each operation is proved to agree with the corresponding operation
on `ℚ[X]`.
-/

namespace Adamar.PolyL

open Polynomial

/-- The polynomial with coefficient list `l`, constant coefficient first. -/
noncomputable def toPoly : List ℚ → ℚ[X]
  | [] => 0
  | a :: l => C a + X * toPoly l

@[simp] lemma toPoly_nil : toPoly [] = 0 := rfl
@[simp] lemma toPoly_cons (a : ℚ) (l : List ℚ) : toPoly (a :: l) = C a + X * toPoly l := rfl

/-! ### Operations -/

/-- Addition. -/
def addL : List ℚ → List ℚ → List ℚ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addL l m

/-- Multiplication by a scalar. -/
def smulL (c : ℚ) (l : List ℚ) : List ℚ := l.map (c * ·)

/-- Negation. -/
def negL (l : List ℚ) : List ℚ := smulL (-1) l

/-- Multiplication. -/
def mulL : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: l, m => addL (smulL a m) (0 :: mulL l m)

/-- Derivative. -/
def derivL : List ℚ → List ℚ
  | [] => []
  | _ :: l => addL l (0 :: derivL l)

/-- Multiplication by `X ^ k`. -/
def shiftL (k : ℕ) (l : List ℚ) : List ℚ := List.replicate k 0 ++ l

/-- Power. -/
def powL (l : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | k + 1 => mulL l (powL l k)

@[simp] lemma toPoly_addL (l m : List ℚ) : toPoly (addL l m) = toPoly l + toPoly m := by
  induction l generalizing m with
  | nil => simp [addL]
  | cons a l ih =>
    cases m with
    | nil => simp [addL]
    | cons b m => simp [addL, ih]; ring

@[simp] lemma toPoly_smulL (c : ℚ) (l : List ℚ) : toPoly (smulL c l) = C c * toPoly l := by
  induction l with
  | nil => simp [smulL]
  | cons a l ih =>
    simp only [smulL, List.map_cons, toPoly_cons] at ih ⊢
    rw [ih, C_mul]
    ring

@[simp] lemma toPoly_negL (l : List ℚ) : toPoly (negL l) = -toPoly l := by
  simp [negL]

@[simp] lemma toPoly_mulL (l m : List ℚ) : toPoly (mulL l m) = toPoly l * toPoly m := by
  induction l with
  | nil => simp [mulL]
  | cons a l ih => simp [mulL, ih]; ring

@[simp] lemma toPoly_derivL (l : List ℚ) : toPoly (derivL l) = derivative (toPoly l) := by
  induction l with
  | nil => simp [derivL]
  | cons a l ih => simp [derivL, ih, derivative_mul]

@[simp] lemma toPoly_shiftL (k : ℕ) (l : List ℚ) : toPoly (shiftL k l) = X ^ k * toPoly l := by
  induction k with
  | zero => simp [shiftL]
  | succ k ih =>
    simp only [shiftL, List.replicate_succ, List.cons_append, toPoly_cons, map_zero,
      zero_add] at ih ⊢
    rw [ih, pow_succ]
    ring

@[simp] lemma toPoly_powL (l : List ℚ) (k : ℕ) : toPoly (powL l k) = toPoly l ^ k := by
  induction k with
  | zero => simp [powL]
  | succ k ih => simp [powL, ih, pow_succ, mul_comm]

/-! ### Trimming trailing zeros -/

/-- Removes the trailing zero coefficients. -/
def trimL : List ℚ → List ℚ
  | [] => []
  | a :: l => if trimL l = [] ∧ a = 0 then [] else a :: trimL l

@[simp] lemma toPoly_trimL (l : List ℚ) : toPoly (trimL l) = toPoly l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [trimL]
    split_ifs with h
    · rw [toPoly_cons, ← ih, h.1, h.2]; simp
    · rw [toPoly_cons, toPoly_cons, ih]

/-- The length of the trimmed list is `natDegree + 1`, or `0` for the zero polynomial. -/
lemma length_trimL (l : List ℚ) :
    (trimL l).length = if toPoly l = 0 then 0 else (toPoly l).natDegree + 1 := by
  induction l with
  | nil => simp [trimL]
  | cons a l ih =>
    by_cases hl : toPoly l = 0
    · have ht : trimL l = [] := by simpa [hl] using ih
      by_cases ha : a = 0
      · simp [trimL, ht, ha, hl]
      · simp [trimL, ht, ha, hl]
    · have ht : trimL l ≠ [] := by
        intro h; rw [h] at ih; simp [hl] at ih
      have hdeg : (toPoly (a :: l)).natDegree = (toPoly l).natDegree + 1 := by
        rw [toPoly_cons, natDegree_add_eq_right_of_natDegree_lt] <;>
          rw [natDegree_X_mul hl]
        rw [natDegree_C]; omega
      have hne : toPoly (a :: l) ≠ 0 := by
        intro h0; have := congr_arg natDegree h0; rw [hdeg] at this
        rw [toPoly_cons] at h0
        have h1 := congr_arg (fun p => p.coeff ((toPoly l).natDegree + 1)) h0
        simp only [coeff_add, coeff_C, coeff_X_mul, coeff_zero] at h1
        simp [leadingCoeff_ne_zero.2 hl] at h1
      simp only [trimL, ht, false_and, ite_false, List.length_cons, ih, ite_eq_right hl, hdeg,
        ite_eq_right hne]

lemma trimL_eq_nil_iff (l : List ℚ) : trimL l = [] ↔ toPoly l = 0 := by
  rw [← List.length_eq_zero_iff, length_trimL]
  split_ifs with h <;> simp [h]

/-- The last entry of the trimmed list is the leading coefficient. -/
lemma getLastD_trimL (l : List ℚ) : (trimL l).getLastD 0 = (toPoly l).leadingCoeff := by
  induction l with
  | nil => simp [trimL]
  | cons a l ih =>
    by_cases hl : toPoly l = 0
    · have ht : trimL l = [] := (trimL_eq_nil_iff l).2 hl
      by_cases ha : a = 0
      · simp [trimL, ht, ha, hl]
      · simp [trimL, ht, ha, hl]
    · have ht : trimL l ≠ [] := fun h => hl ((trimL_eq_nil_iff l).1 h)
      have hlc : (toPoly (a :: l)).leadingCoeff = (toPoly l).leadingCoeff := by
        rw [toPoly_cons, leadingCoeff_add_of_degree_lt, mul_comm, leadingCoeff_mul_X]
        refine degree_lt_degree ?_
        rw [natDegree_C, natDegree_X_mul hl]
        omega
      obtain ⟨b, t, hbt⟩ := List.exists_cons_of_ne_nil ht
      simp only [trimL, hlc, ← ih, hbt, List.getLastD_cons, List.cons_ne_nil, false_and,
        ite_false]

lemma length_trimL_le (l : List ℚ) : (trimL l).length ≤ l.length := by
  induction l with
  | nil => simp [trimL]
  | cons a l ih =>
    simp only [trimL]
    split_ifs <;> simp; omega

lemma natDegree_toPoly_lt {l : List ℚ} (h : toPoly l ≠ 0) : (toPoly l).natDegree < l.length := by
  have := length_trimL_le l
  rw [length_trimL, ite_eq_right h] at this
  omega

/-! ### Euclidean remainder -/

/-- Characterization of the remainder of the Euclidean division. -/
lemma mod_eq_of {P M S R : ℚ[X]} (hM : M ≠ 0) (h : P = M * S + R)
    (hR : R.degree < M.degree) : P % M = R := by
  rw [mod_def]
  refine (div_modByMonic_unique (C M.leadingCoeff * S) R (monic_mul_leadingCoeff_inv hM)
    ⟨?_, by rwa [degree_mul_leadingCoeff_inv _ hM]⟩).2
  rw [h, mul_assoc, ← mul_assoc (C _), ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.2 hM),
    C_1, one_mul, add_comm]

/-- One step of the Euclidean division: cancels the leading coefficient of `l`. -/
def modStep (l m : List ℚ) : List ℚ :=
  let l' := trimL l
  let m' := trimL m
  addL l' (smulL (-(l'.getLastD 0 / m'.getLastD 0)) (shiftL (l'.length - m'.length) m'))

lemma toPoly_modStep {l m : List ℚ} (hl : toPoly l ≠ 0) (hm : toPoly m ≠ 0) :
    toPoly (modStep l m) = toPoly l - C ((toPoly l).leadingCoeff / (toPoly m).leadingCoeff) *
      X ^ ((toPoly l).natDegree - (toPoly m).natDegree) * toPoly m := by
  simp only [modStep, toPoly_addL, toPoly_trimL, toPoly_smulL, toPoly_shiftL, getLastD_trimL,
    length_trimL, ite_eq_right hl, ite_eq_right hm, map_neg]
  rw [show (toPoly l).natDegree + 1 - ((toPoly m).natDegree + 1) =
    (toPoly l).natDegree - (toPoly m).natDegree by omega]
  ring

lemma degree_modStep_lt {l m : List ℚ} (hl : toPoly l ≠ 0) (hm : toPoly m ≠ 0)
    (hdeg : (toPoly m).natDegree ≤ (toPoly l).natDegree) :
    (toPoly (modStep l m)).degree < (toPoly l).degree := by
  rw [toPoly_modStep hl hm]
  have hc : (toPoly l).leadingCoeff / (toPoly m).leadingCoeff ≠ 0 :=
    div_ne_zero (leadingCoeff_ne_zero.2 hl) (leadingCoeff_ne_zero.2 hm)
  refine degree_sub_lt_left ?_ hl ?_
  · rw [degree_mul, degree_C_mul_X_pow _ hc, degree_eq_natDegree hl, degree_eq_natDegree hm]
    norm_cast
    omega
  · rw [leadingCoeff_mul, leadingCoeff_C_mul_X_pow,
      div_mul_cancel₀ _ (leadingCoeff_ne_zero.2 hm)]

/-- Iterated Euclidean division steps. -/
def modAux : ℕ → List ℚ → List ℚ → List ℚ
  | 0, l, _ => l
  | fuel + 1, l, m =>
    if (trimL l).length < (trimL m).length then l else modAux fuel (modStep l m) m

lemma modAux_spec {m : List ℚ} (hm : toPoly m ≠ 0) (fuel : ℕ) (l : List ℚ) :
    (∃ S, toPoly l = toPoly m * S + toPoly (modAux fuel l m)) ∧
      ((trimL l).length ≤ fuel → (trimL (modAux fuel l m)).length < (trimL m).length) := by
  induction fuel generalizing l with
  | zero =>
    refine ⟨⟨0, by simp [modAux]⟩, fun h => ?_⟩
    simp only [modAux]
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 h), List.length_nil]
    exact List.length_pos_of_ne_nil fun h0 => hm ((trimL_eq_nil_iff m).1 h0)
  | succ fuel ih =>
    simp only [modAux]
    split_ifs with hlt
    · exact ⟨⟨0, by simp⟩, fun _ => hlt⟩
    · have hl : toPoly l ≠ 0 := by
        intro h0
        rw [length_trimL, length_trimL, ite_eq_left h0, ite_eq_right hm] at hlt
        omega
      have hdeg : (toPoly m).natDegree ≤ (toPoly l).natDegree := by
        rw [length_trimL, length_trimL, ite_eq_right hl, ite_eq_right hm] at hlt
        omega
      have hstep := degree_modStep_lt hl hm hdeg
      obtain ⟨⟨S, hS⟩, hlen⟩ := ih (modStep l m)
      refine ⟨⟨S + C ((toPoly l).leadingCoeff / (toPoly m).leadingCoeff) *
        X ^ ((toPoly l).natDegree - (toPoly m).natDegree), ?_⟩, fun h => hlen ?_⟩
      · have := toPoly_modStep hl hm
        linear_combination hS - this
      · rw [length_trimL, length_trimL, ite_eq_right hl] at *
        split_ifs with h0
        · omega
        · have := natDegree_lt_natDegree h0 hstep
          omega

/-- The remainder of the Euclidean division. -/
def modL (l m : List ℚ) : List ℚ := if trimL m = [] then l else modAux (l.length + 1) l m

@[simp] lemma toPoly_modL (l m : List ℚ) : toPoly (modL l m) = toPoly l % toPoly m := by
  unfold modL
  split_ifs with h
  · rw [(trimL_eq_nil_iff m).1 h, EuclideanDomain.mod_zero]
  · have hm : toPoly m ≠ 0 := fun h0 => h ((trimL_eq_nil_iff m).2 h0)
    obtain ⟨⟨S, hS⟩, hlen⟩ := modAux_spec hm (l.length + 1) l
    have hlen := hlen ((length_trimL_le l).trans (Nat.le_succ _))
    refine (mod_eq_of hm hS ?_).symm
    rw [length_trimL, length_trimL, ite_eq_right hm] at hlen
    split_ifs at hlen with h0
    · rw [h0, degree_zero]
      exact bot_lt_iff_ne_bot.2 (degree_ne_bot.2 hm)
    · exact degree_lt_degree (by omega)

/-! ### Sturm sequences -/

/-- The Sturm sequence, computed with `fuel` steps at most. -/
def sturmAux : ℕ → List ℚ → List ℚ → List (List ℚ)
  | 0, _, _ => []
  | fuel + 1, p, q => if trimL p = [] then [] else p :: sturmAux fuel q (negL (modL p q))

/-- The Sturm sequence of `p` and `q`. -/
def sturmL (p q : List ℚ) : List (List ℚ) := sturmAux (q.length + 2) p q

lemma map_sturmAux (fuel : ℕ) (p q : List ℚ)
    (hfuel : (if toPoly p = 0 then 0 else if toPoly q = 0 then 1 else 2 + (toPoly q).natDegree)
      ≤ fuel) :
    (sturmAux fuel p q).map toPoly = sturmSeq (toPoly p) (toPoly q) := by
  induction fuel generalizing p q with
  | zero =>
    have hp : toPoly p = 0 := by by_contra h; rw [ite_eq_right h] at hfuel; split_ifs at hfuel <;> omega
    simp [sturmAux, hp]
  | succ fuel ih =>
    by_cases hp : toPoly p = 0
    · simp [sturmAux, (trimL_eq_nil_iff p).2 hp, hp]
    rw [sturmAux, ite_eq_right (fun h => hp ((trimL_eq_nil_iff p).1 h)), List.map_cons,
      sturmSeq_cons hp, ih]
    · simp [neg_mod]
    · rw [ite_eq_right hp] at hfuel
      simp only [toPoly_negL, toPoly_modL, neg_eq_zero, natDegree_neg]
      by_cases hq : toPoly q = 0
      · simp [hq]
      · rw [ite_eq_right hq] at hfuel
        rw [ite_eq_right hq]
        by_cases hr : toPoly p % toPoly q = 0
        · rw [ite_eq_left hr]; omega
        · rw [ite_eq_right hr]
          have := natDegree_lt_natDegree hr (degree_mod_lt (toPoly p) hq)
          omega

@[simp] lemma map_sturmL (p q : List ℚ) :
    (sturmL p q).map toPoly = sturmSeq (toPoly p) (toPoly q) := by
  refine map_sturmAux _ p q ?_
  split_ifs with h1 h2 <;> try omega
  have := natDegree_toPoly_lt h2
  omega

end Adamar.PolyL
