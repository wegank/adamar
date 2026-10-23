/-
Copyright (c) 2026 Weijia Wang. All rights reserved.
-/
import Mathlib

/-!
# The Sturm–Tarski theorem

This file is *not* part of the Coq development `signdet.v`. We prove the Sturm–Tarski theorem
(*Algorithms in Real Algebraic Geometry*, Theorem 2.58), which computes the Tarski query
`TaQ(Q, P) = ∑_{x ∈ ℝ, P(x) = 0} sign (Q x)` from the coefficients of `P` and `Q`, as a
difference of numbers of sign variations of the Sturm sequence `Polynomial.sturmSeq P (P' Q)`
(the signed remainder sequence) at `-∞` and `+∞`.

Together with `Adamar.sign_determination_roots`, this makes the sign determination for the
roots of a univariate polynomial effective: the numbers of roots of `P` realizing each sign
condition of `Q₀, …, Q_{n-1}` are linear combinations of numbers of sign variations of Sturm
sequences.

## Strategy

We follow the proof of the book through Cauchy indices, working with twice the Cauchy index to
stay in `ℤ`.

* `Adamar.sgnR F x` and `Adamar.sgnL F x` are the signs of `F` just right and just left of
  `x`, defined algebraically from the factorization `F = (X - x) ^ μ * G` with `G x ≠ 0`.
  They coincide with the signs of `F` on intervals free of roots of `F`
  (`Adamar.sign_eval_eq_sgnR`, `Adamar.sign_eval_eq_sgnL`).
* Telescoping (`Adamar.sign_sub_sign_eq_sum_cross`): for `F a ≠ 0 ≠ F b`, the variation
  `sign F(b) - sign F(a)` is the sum over the roots of `F` in `(a, b)` of
  `sgnR F x - sgnL F x`.
* `Adamar.ind2 P Q a b` is twice the Cauchy index of `Q / P` on `(a, b)`. It satisfies the
  inversion formula (`Adamar.ind2_add_ind2`), only depends on `Q` modulo `P`
  (`Adamar.ind2_add_mul`), and `ind2 P (P' Q) a b` is twice the Tarski query of `Q` on the
  roots of `P` in `(a, b)` (`Adamar.ind2_derivative_mul`).
* By induction along the Sturm sequence, `Var(a) - Var(b)` is the Cauchy index
  (`Adamar.two_mul_varAt_sub_varAt`), and letting `a → -∞`, `b → +∞` gives the theorem.
-/

namespace Adamar

open Polynomial Finset

noncomputable section

/-! ### Local signs -/

/-- The cofactor `G` in the factorization `F = (X - x) ^ μ * G` with `μ` the multiplicity of
`x` as a root of `F`. -/
def cofactor (F : ℝ[X]) (x : ℝ) : ℝ[X] := F /ₘ (X - C x) ^ rootMultiplicity x F

lemma pow_mul_cofactor (F : ℝ[X]) (x : ℝ) :
    (X - C x) ^ rootMultiplicity x F * cofactor F x = F :=
  pow_mul_divByMonic_rootMultiplicity_eq F x

lemma eval_cofactor_ne_zero {F : ℝ[X]} (hF : F ≠ 0) (x : ℝ) : (cofactor F x).eval x ≠ 0 :=
  eval_divByMonic_pow_rootMultiplicity_ne_zero x hF

/-- The sign of `F` just right of `x`. -/
def sgnR (F : ℝ[X]) (x : ℝ) : ℤ := SignType.sign ((cofactor F x).eval x)

/-- The sign of `F` just left of `x`. -/
def sgnL (F : ℝ[X]) (x : ℝ) : ℤ := (-1) ^ rootMultiplicity x F * sgnR F x

/-- The local data of a factorization `F = (X - x) ^ m * G` with `G x ≠ 0`. -/
lemma rootMultiplicity_cofactor_of_eq {F G : ℝ[X]} {x : ℝ} {m : ℕ}
    (hF : F = (X - C x) ^ m * G) (hG : G.eval x ≠ 0) :
    rootMultiplicity x F = m ∧ cofactor F x = G := by
  have hG0 : G ≠ 0 := fun h => hG (by simp [h])
  have hpow : ((X - C x) ^ m : ℝ[X]) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero x)
  have hm : rootMultiplicity x F = m := by
    rw [hF, rootMultiplicity_mul (mul_ne_zero hpow hG0), rootMultiplicity_X_sub_C_pow,
      rootMultiplicity_eq_zero hG, add_zero]
  refine ⟨hm, ?_⟩
  have := pow_mul_cofactor F x
  rw [hm] at this
  conv_rhs at this => rw [hF]
  exact mul_left_cancel₀ hpow this

lemma sgnR_of_eq {F G : ℝ[X]} {x : ℝ} {m : ℕ} (hF : F = (X - C x) ^ m * G)
    (hG : G.eval x ≠ 0) : sgnR F x = SignType.sign (G.eval x) := by
  rw [sgnR, (rootMultiplicity_cofactor_of_eq hF hG).2]

@[simp] lemma sgnR_zero (x : ℝ) : sgnR 0 x = 0 := by
  simp [sgnR, cofactor]

@[simp] lemma sgnL_zero (x : ℝ) : sgnL 0 x = 0 := by
  simp [sgnL]

lemma sgnR_ne_zero {F : ℝ[X]} (hF : F ≠ 0) (x : ℝ) : sgnR F x ≠ 0 := by
  intro h
  apply eval_cofactor_ne_zero hF x
  rw [sgnR] at h
  have key : ∀ s : SignType, (s : ℤ) = 0 → s = 0 := by decide
  exact sign_eq_zero_iff.1 (key _ h)

lemma sgnR_of_eval_ne_zero {F : ℝ[X]} {x : ℝ} (hx : F.eval x ≠ 0) :
    sgnR F x = SignType.sign (F.eval x) :=
  sgnR_of_eq (m := 0) (by simp) hx

lemma sgnR_mul (F G : ℝ[X]) (x : ℝ) : sgnR (F * G) x = sgnR F x * sgnR G x := by
  rcases eq_or_ne F 0 with rfl | hF
  · simp
  rcases eq_or_ne G 0 with rfl | hG
  · simp
  have h : F * G = (X - C x) ^ (rootMultiplicity x F + rootMultiplicity x G) *
      (cofactor F x * cofactor G x) := by
    conv_lhs => rw [← pow_mul_cofactor F x, ← pow_mul_cofactor G x]
    ring
  rw [sgnR_of_eq h (by simpa using ⟨eval_cofactor_ne_zero hF x, eval_cofactor_ne_zero hG x⟩),
    eval_mul, sign_mul, sgnR, sgnR]
  push_cast
  rfl

lemma rootMultiplicity_mul' {F G : ℝ[X]} (hF : F ≠ 0) (hG : G ≠ 0) (x : ℝ) :
    rootMultiplicity x (F * G) = rootMultiplicity x F + rootMultiplicity x G :=
  rootMultiplicity_mul (mul_ne_zero hF hG)

lemma sgnR_neg (F : ℝ[X]) (x : ℝ) : sgnR (-F) x = -sgnR F x := by
  have : -F = C (-1) * F := by simp
  rw [this, sgnR_mul, sgnR_of_eval_ne_zero (by simp)]
  simp

lemma rootMultiplicity_neg' (F : ℝ[X]) (x : ℝ) :
    rootMultiplicity x (-F) = rootMultiplicity x F := by
  rcases eq_or_ne F 0 with rfl | hF
  · simp
  have : -F = C (-1) * F := by simp
  rw [this, rootMultiplicity_mul' (by simp) hF, rootMultiplicity_eq_zero (by simp), zero_add]

/-- Adding a polynomial vanishing to a higher order at `x` does not change the local data. -/
lemma sgnR_add_of_lt {F G : ℝ[X]} {x : ℝ} (hF : F ≠ 0)
    (h : G = 0 ∨ rootMultiplicity x F < rootMultiplicity x G) :
    rootMultiplicity x (F + G) = rootMultiplicity x F ∧ sgnR (F + G) x = sgnR F x := by
  rcases h with rfl | h
  · simp
  set m := rootMultiplicity x F
  set n := rootMultiplicity x G
  have hsum : F + G = (X - C x) ^ m * (cofactor F x + (X - C x) ^ (n - m) * cofactor G x) := by
    conv_lhs => rw [← pow_mul_cofactor F x, ← pow_mul_cofactor G x]
    rw [mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h.le]
  have hev : (cofactor F x + (X - C x) ^ (n - m) * cofactor G x).eval x = (cofactor F x).eval x := by
    simp [Nat.sub_ne_zero_of_lt h]
  have hne : (cofactor F x + (X - C x) ^ (n - m) * cofactor G x).eval x ≠ 0 := by
    rw [hev]; exact eval_cofactor_ne_zero hF x
  obtain ⟨h1, h2⟩ := rootMultiplicity_cofactor_of_eq hsum hne
  exact ⟨h1, by rw [sgnR, h2, hev, sgnR]⟩

/-! ### Signs on intervals free of roots -/

/-- A polynomial with no root on `[a, b]` has constant sign there. -/
lemma sign_eval_eq_of_forall_ne_zero {F : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ z ∈ Set.Icc a b, F.eval z ≠ 0) :
    SignType.sign (F.eval a) = SignType.sign (F.eval b) := by
  have hc : ContinuousOn (fun z => F.eval z) (Set.Icc a b) := F.continuous.continuousOn
  have ha := h a ⟨le_rfl, hab⟩
  have hb := h b ⟨hab, le_rfl⟩
  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
  · rw [sign_neg ha', sign_neg hb']
  · obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hab hc ⟨ha'.le, hb'.le⟩
    exact absurd hz0 (h z hz)
  · obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hab hc ⟨hb'.le, ha'.le⟩
    exact absurd hz0 (h z hz)
  · rw [sign_pos ha', sign_pos hb']

lemma eval_eq_pow_mul_cofactor (F : ℝ[X]) (x y : ℝ) :
    F.eval y = (y - x) ^ rootMultiplicity x F * (cofactor F x).eval y := by
  conv_lhs => rw [← pow_mul_cofactor F x]
  simp

/-- If `G = cofactor F x` and `F` has no root in `I \ {x}`, then `G` has no root in `I`. -/
lemma eval_cofactor_ne_zero_of {F : ℝ[X]} (hF : F ≠ 0) {x z : ℝ}
    (h : z ≠ x → F.eval z ≠ 0) : (cofactor F x).eval z ≠ 0 := by
  rcases eq_or_ne z x with rfl | hzx
  · exact eval_cofactor_ne_zero hF z
  · intro h0
    exact h hzx (by rw [eval_eq_pow_mul_cofactor F x z, h0, mul_zero])

/-- `sgnR F x` is the sign of `F` on any interval `(x, y]` free of roots of `F`. -/
lemma sign_eval_eq_sgnR {F : ℝ[X]} (hF : F ≠ 0) {x y : ℝ} (hxy : x < y)
    (h : ∀ z ∈ Set.Ioc x y, F.eval z ≠ 0) : (SignType.sign (F.eval y) : ℤ) = sgnR F x := by
  have hG : SignType.sign ((cofactor F x).eval x) = SignType.sign ((cofactor F x).eval y) :=
    sign_eval_eq_of_forall_ne_zero hxy.le fun z hz => eval_cofactor_ne_zero_of hF fun hzx =>
      h z ⟨lt_of_le_of_ne hz.1 (Ne.symm hzx), hz.2⟩
  rw [eval_eq_pow_mul_cofactor F x y, sign_mul, sign_pow, sign_pos (sub_pos.2 hxy), one_pow,
    one_mul, sgnR, hG]

/-- `sgnL F x` is the sign of `F` on any interval `[y, x)` free of roots of `F`. -/
lemma sign_eval_eq_sgnL {F : ℝ[X]} (hF : F ≠ 0) {x y : ℝ} (hyx : y < x)
    (h : ∀ z ∈ Set.Ico y x, F.eval z ≠ 0) : (SignType.sign (F.eval y) : ℤ) = sgnL F x := by
  have hG : SignType.sign ((cofactor F x).eval y) = SignType.sign ((cofactor F x).eval x) :=
    sign_eval_eq_of_forall_ne_zero hyx.le fun z hz => eval_cofactor_ne_zero_of hF fun hzx =>
      h z ⟨hz.1, lt_of_le_of_ne hz.2 hzx⟩
  rw [eval_eq_pow_mul_cofactor F x y, sign_mul, sign_pow, sign_neg (sub_neg.2 hyx), sgnL, sgnR,
    hG]
  push_cast
  rfl

/-! ### Telescoping -/

/-- The roots of `F` in the open interval `(a, b)`. -/
def rootsIn (F : ℝ[X]) (a b : ℝ) : Finset ℝ := F.roots.toFinset.filter fun x => a < x ∧ x < b

lemma mem_rootsIn {F : ℝ[X]} {a b x : ℝ} :
    x ∈ rootsIn F a b ↔ (F ≠ 0 ∧ F.eval x = 0) ∧ a < x ∧ x < b := by
  simp [rootsIn, mem_roots', IsRoot]

/-- The jump `sgnR F x - sgnL F x` of the sign of `F` at `x`. -/
def cross (F : ℝ[X]) (x : ℝ) : ℤ := sgnR F x - sgnL F x

/-- The variation of the sign of `F` between two non-roots is the sum of the jumps of its sign
at the roots in between. -/
theorem sign_sub_sign_eq_sum_cross {F : ℝ[X]} (hF : F ≠ 0) {a b : ℝ} (hab : a < b)
    (ha : F.eval a ≠ 0) (hb : F.eval b ≠ 0) :
    (SignType.sign (F.eval b) : ℤ) - SignType.sign (F.eval a) =
      ∑ x ∈ rootsIn F a b, cross F x := by
  induction hn : (rootsIn F a b).card using Nat.strong_induction_on generalizing b with
  | _ n ih =>
  rcases (rootsIn F a b).eq_empty_or_nonempty with h0 | hne
  · rw [h0, sum_empty, sub_eq_zero]
    have := sign_eval_eq_of_forall_ne_zero hab.le (F := F) fun z hz hz0 => by
      rcases eq_or_lt_of_le hz.1 with rfl | h1
      · exact ha hz0
      rcases eq_or_lt_of_le hz.2 with rfl | h2
      · exact hb hz0
      have : z ∈ rootsIn F a b := mem_rootsIn.2 ⟨⟨hF, hz0⟩, h1, h2⟩
      simp [h0] at this
    rw [this]
  set x := (rootsIn F a b).max' hne with hxdef
  have hx : x ∈ rootsIn F a b := max'_mem _ _
  obtain ⟨-, hax, hxb⟩ := mem_rootsIn.1 hx
  -- A root of `F` in `(a, b)` other than `x` lies in `L`, and is smaller than `x`.
  set L := (rootsIn F a b).erase x with hL
  have hlt : ∀ z ∈ rootsIn F a b, z ≤ x := fun z hz => le_max' _ z hz
  -- The sign of `F` at `b` is its sign right of `x`.
  have hR : (SignType.sign (F.eval b) : ℤ) = sgnR F x := by
    refine sign_eval_eq_sgnR hF hxb fun z hz hz0 => ?_
    rcases eq_or_lt_of_le hz.2 with rfl | h2
    · exact hb hz0
    exact absurd (hlt z (mem_rootsIn.2 ⟨⟨hF, hz0⟩, hax.trans hz.1, h2⟩)) (not_le.2 hz.1)
  rw [← insert_erase hx, sum_insert (notMem_erase x _), ← hL, hR, cross]
  rcases L.eq_empty_or_nonempty with hL0 | hLne
  · -- No other root: the sign of `F` at `a` is its sign left of `x`.
    rw [hL0, sum_empty, add_zero]
    have : (SignType.sign (F.eval a) : ℤ) = sgnL F x := by
      refine sign_eval_eq_sgnL hF hax fun z hz hz0 => ?_
      rcases eq_or_lt_of_le hz.1 with rfl | h1
      · exact ha hz0
      have hzL : z ∈ L := mem_erase.2 ⟨ne_of_lt hz.2, mem_rootsIn.2 ⟨⟨hF, hz0⟩, h1,
        hz.2.trans hxb⟩⟩
      simp [hL0] at hzL
    rw [this]
  · -- Otherwise, cut at a point `u` between the largest root `x'` of `L` and `x`.
    set x' := L.max' hLne
    have hx' : x' ∈ L := max'_mem _ _
    have hx'x : x' < x := lt_of_le_of_ne (hlt x' (mem_of_mem_erase hx')) (ne_of_mem_erase hx')
    obtain ⟨-, hax', -⟩ := mem_rootsIn.1 (mem_of_mem_erase hx')
    set u := (x' + x) / 2
    have hx'u : x' < u := by simp only [u]; linarith
    have hux : u < x := by simp only [u]; linarith
    have hnoroot : ∀ z ∈ Set.Ico u x, F.eval z ≠ 0 := fun z hz hz0 => by
      have hzL : z ∈ L := mem_erase.2 ⟨ne_of_lt hz.2, mem_rootsIn.2 ⟨⟨hF, hz0⟩,
        hax'.trans (hx'u.trans_le hz.1), hz.2.trans hxb⟩⟩
      exact absurd (le_max' L z hzL) (not_le.2 (hx'u.trans_le hz.1))
    have hu : F.eval u ≠ 0 := hnoroot u ⟨le_rfl, hux⟩
    have hLu : rootsIn F a u = L := by
      ext z
      constructor
      · intro hz
        obtain ⟨hz0, h1, h2⟩ := mem_rootsIn.1 hz
        exact mem_erase.2 ⟨ne_of_lt (h2.trans hux), mem_rootsIn.2 ⟨hz0, h1, (h2.trans hux).trans hxb⟩⟩
      · intro hz
        obtain ⟨hz0, h1, -⟩ := mem_rootsIn.1 (mem_of_mem_erase hz)
        exact mem_rootsIn.2 ⟨hz0, h1, (le_max' L z hz).trans_lt hx'u⟩
    have hcard : L.card < n := by
      rw [← hn, hL]
      exact card_erase_lt_of_mem hx
    have hIH := ih L.card hcard (hax'.trans hx'u) hu (by rw [hLu])
    rw [hLu] at hIH
    rw [← hIH, ← sign_eval_eq_sgnL hF hux hnoroot]
    ring

/-! ### Cauchy index -/

lemma cross_eq (F : ℝ[X]) (x : ℝ) :
    cross F x = sgnR F x * (1 - (-1) ^ rootMultiplicity x F) := by
  unfold cross sgnL
  ring

lemma sgnR_mul_self {F : ℝ[X]} (hF : F ≠ 0) (x : ℝ) : sgnR F x * sgnR F x = 1 := by
  have h := sgnR_ne_zero hF x
  unfold sgnR at h ⊢
  generalize SignType.sign ((cofactor F x).eval x) = t at h ⊢
  cases t <;> simp_all

/-- Twice the jump of the Cauchy index of `Q / P` at `x`: it is non-zero only if `x` is a pole
of odd order of `Q / P`, in which case it is `±2`, according to the sign change of `Q / P`. -/
def jump2 (P Q : ℝ[X]) (x : ℝ) : ℤ :=
  if rootMultiplicity x Q < rootMultiplicity x P then
    sgnR P x * sgnR Q x * (1 - (-1) ^ (rootMultiplicity x P + rootMultiplicity x Q))
  else 0

/-- Twice the Cauchy index of `Q / P` on `(a, b)`. -/
def ind2 (P Q : ℝ[X]) (a b : ℝ) : ℤ := ∑ x ∈ rootsIn P a b, jump2 P Q x

lemma jump2_of_eval_ne_zero {P : ℝ[X]} {x : ℝ} (hx : P.eval x ≠ 0) (Q : ℝ[X]) :
    jump2 P Q x = 0 := by
  simp [jump2, rootMultiplicity_eq_zero hx]

@[simp] lemma jump2_zero_right (P : ℝ[X]) (x : ℝ) : jump2 P 0 x = 0 := by
  simp [jump2]

lemma jump2_of_le {P Q : ℝ[X]} {x : ℝ} (h : rootMultiplicity x P ≤ rootMultiplicity x Q) :
    jump2 P Q x = 0 := by
  simp [jump2, not_lt.2 h]

lemma jump2_add_jump2 {P Q : ℝ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) (x : ℝ) :
    jump2 P Q x + jump2 Q P x = cross (P * Q) x := by
  rw [cross_eq, sgnR_mul, rootMultiplicity_mul' hP hQ]
  rcases lt_trichotomy (rootMultiplicity x Q) (rootMultiplicity x P) with h | h | h
  · rw [jump2_of_le h.le, add_zero, jump2, ite_eq_left h]
  · rw [jump2_of_le h.ge, jump2_of_le h.le, h, add_zero, ← two_mul, pow_mul]
    simp
  · rw [jump2_of_le h.le, zero_add, jump2, ite_eq_left h]
    ring

@[simp] lemma ind2_zero_left (Q : ℝ[X]) (a b : ℝ) : ind2 0 Q a b = 0 := by
  simp [ind2, rootsIn]

@[simp] lemma ind2_zero_right (P : ℝ[X]) (a b : ℝ) : ind2 P 0 a b = 0 := by
  simp [ind2]

lemma rootsIn_subset_mul {P Q : ℝ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) (a b : ℝ) :
    rootsIn P a b ⊆ rootsIn (P * Q) a b := fun x hx => by
  obtain ⟨⟨-, hx0⟩, h⟩ := mem_rootsIn.1 hx
  exact mem_rootsIn.2 ⟨⟨mul_ne_zero hP hQ, by simp [hx0]⟩, h⟩

/-- **Inversion formula** for Cauchy indices. -/
theorem ind2_add_ind2 {P Q : ℝ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) {a b : ℝ} (hab : a < b)
    (ha : (P * Q).eval a ≠ 0) (hb : (P * Q).eval b ≠ 0) :
    ind2 P Q a b + ind2 Q P a b =
      SignType.sign ((P * Q).eval b) - SignType.sign ((P * Q).eval a) := by
  have hPQ := rootsIn_subset_mul hP hQ a b
  have hQP : rootsIn Q a b ⊆ rootsIn (P * Q) a b := by
    rw [mul_comm]; exact rootsIn_subset_mul hQ hP a b
  rw [ind2, ind2, sum_subset hPQ fun x _ hx => jump2_of_eval_ne_zero (fun h => hx
      (mem_rootsIn.2 ⟨⟨hP, h⟩, (mem_rootsIn.1 ‹_›).2⟩)) Q,
    sum_subset hQP fun x _ hx => jump2_of_eval_ne_zero (fun h => hx
      (mem_rootsIn.2 ⟨⟨hQ, h⟩, (mem_rootsIn.1 ‹_›).2⟩)) P,
    ← sum_add_distrib, sign_sub_sign_eq_sum_cross (mul_ne_zero hP hQ) hab ha hb]
  exact sum_congr rfl fun x _ => jump2_add_jump2 hP hQ x

/-- The Cauchy index of `Q / P` only depends on `Q` modulo `P`. -/
theorem ind2_add_mul {P : ℝ[X]} (hP : P ≠ 0) (Q S : ℝ[X]) (a b : ℝ) :
    ind2 P (Q + S * P) a b = ind2 P Q a b := by
  refine sum_congr rfl fun x hx => ?_
  obtain ⟨⟨-, hx0⟩, -⟩ := mem_rootsIn.1 hx
  have hm : 0 < rootMultiplicity x P := (rootMultiplicity_pos hP).2 hx0
  -- `S * P` vanishes at `x` to order at least that of `P`.
  have hSP : S * P = 0 ∨ rootMultiplicity x P ≤ rootMultiplicity x (S * P) := by
    rcases eq_or_ne S 0 with rfl | hS
    · simp
    · right; rw [rootMultiplicity_mul' hS hP]; omega
  rcases eq_or_ne Q 0 with rfl | hQ
  · rw [zero_add, jump2_zero_right]
    rcases hSP with h | h
    · rw [h, jump2_zero_right]
    · exact jump2_of_le h
  rcases lt_or_ge (rootMultiplicity x Q) (rootMultiplicity x P) with h | h
  · obtain ⟨h1, h2⟩ := sgnR_add_of_lt (x := x) hQ (hSP.imp id fun h' => h.trans_le h')
    simp only [jump2, h1, h2]
  · rw [jump2_of_le h]
    rcases eq_or_ne (Q + S * P) 0 with h0 | h0
    · rw [h0, jump2_zero_right]
    refine jump2_of_le ?_
    rcases hSP with h' | h'
    · rw [h', add_zero]; exact h
    · exact (le_min h h').trans (rootMultiplicity_add x h0)

lemma ind2_neg (P Q : ℝ[X]) (a b : ℝ) : ind2 P (-Q) a b = -ind2 P Q a b := by
  rw [ind2, ind2, ← sum_neg_distrib]
  refine sum_congr rfl fun x _ => ?_
  simp only [jump2, rootMultiplicity_neg', sgnR_neg]
  split_ifs <;> ring

/-! ### The Cauchy index of `P' Q / P` -/

lemma derivative_ne_zero_of_root {P : ℝ[X]} (hP : P ≠ 0) {x : ℝ} (hx : P.eval x = 0) :
    derivative P ≠ 0 := by
  intro h
  have hc := eq_C_of_derivative_eq_zero h
  rw [hc, eval_C] at hx
  exact hP (by rw [hc, hx, C_0])

lemma sgnR_derivative {P : ℝ[X]} (hP : P ≠ 0) {x : ℝ} (hx : P.eval x = 0) :
    sgnR (derivative P) x = sgnR P x := by
  set m := rootMultiplicity x P
  set G := cofactor P x
  have hm : 0 < m := (rootMultiplicity_pos hP).2 hx
  have hd : derivative P = (X - C x) ^ (m - 1) * (C (m : ℝ) * G + (X - C x) * derivative G) := by
    conv_lhs => rw [← pow_mul_cofactor P x]
    rw [derivative_mul, derivative_X_sub_C_pow]
    have : (X - C x) ^ m = (X - C x) ^ (m - 1) * (X - C x) := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    rw [this]
    ring
  have hev : (C (m : ℝ) * G + (X - C x) * derivative G).eval x = m * G.eval x := by simp
  have hG := eval_cofactor_ne_zero hP x
  rw [sgnR_of_eq hd (by rw [hev]; exact mul_ne_zero (by exact_mod_cast hm.ne') hG), hev,
    sign_mul, sign_pos (by exact_mod_cast hm : (0 : ℝ) < m), one_mul, sgnR]

/-- The Cauchy index of `P' Q / P` is the Tarski query of `Q` on the roots of `P`. -/
theorem ind2_derivative_mul {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X]) (a b : ℝ) :
    ind2 P (derivative P * Q) a b = 2 * ∑ x ∈ rootsIn P a b, (SignType.sign (Q.eval x) : ℤ) := by
  rw [ind2, mul_sum]
  refine sum_congr rfl fun x hx => ?_
  obtain ⟨⟨-, hx0⟩, -⟩ := mem_rootsIn.1 hx
  have hm : 0 < rootMultiplicity x P := (rootMultiplicity_pos hP).2 hx0
  have hd := derivative_ne_zero_of_root hP hx0
  have hdm : rootMultiplicity x (derivative P) = rootMultiplicity x P - 1 :=
    derivative_rootMultiplicity_of_root hx0
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp
  rcases eq_or_ne (Q.eval x) 0 with hQx | hQx
  · rw [hQx, sign_zero, SignType.coe_zero, mul_zero]
    refine jump2_of_le ?_
    rw [rootMultiplicity_mul' hd hQ, hdm]
    have : 0 < rootMultiplicity x Q := (rootMultiplicity_pos hQ).2 hQx
    omega
  · have hQm : rootMultiplicity x Q = 0 := rootMultiplicity_eq_zero hQx
    have hlt : rootMultiplicity x (derivative P * Q) < rootMultiplicity x P := by
      rw [rootMultiplicity_mul' hd hQ, hdm, hQm]; omega
    rw [jump2, ite_eq_left hlt, sgnR_mul, sgnR_derivative hP hx0, sgnR_of_eval_ne_zero hQx,
      rootMultiplicity_mul' hd hQ, hdm, hQm, add_zero]
    have hodd : Odd (rootMultiplicity x P + (rootMultiplicity x P - 1)) := ⟨rootMultiplicity x P - 1, by omega⟩
    rw [hodd.neg_one_pow]
    have := sgnR_mul_self hP x
    linear_combination (2 * (SignType.sign (Q.eval x) : ℤ)) * this

/-! ### Sign variations along the Sturm sequence -/

/-- The number of sign variations of a list of polynomials evaluated at `t`. -/
def varAt (l : List ℝ[X]) (t : ℝ) : ℕ := (l.map fun p => p.eval t).signVariations

lemma two_mul_ite_sign {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    (2 * (if SignType.sign u = SignType.sign v then 0 else 1 : ℕ) : ℤ) =
      1 - SignType.sign (u * v) := by
  rcases lt_or_gt_of_ne hu with hu | hu <;> rcases lt_or_gt_of_ne hv with hv | hv <;>
    simp [sign_neg, sign_pos, hu, hv, mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos,
      mul_neg_of_pos_of_neg]

/-- **Sign variations and Cauchy index.** If `a < b` are not roots of any polynomial in the
Sturm sequence of `P` and `Q`, the difference of the numbers of sign variations of the sequence
at `a` and at `b` is the Cauchy index of `Q / P` on `(a, b)`. -/
theorem two_mul_varAt_sub_varAt (P Q : ℝ[X]) {a b : ℝ} (hab : a < b)
    (h : ∀ p ∈ sturmSeq P Q, p.eval a ≠ 0 ∧ p.eval b ≠ 0) :
    2 * ((varAt (sturmSeq P Q) a : ℤ) - varAt (sturmSeq P Q) b) = ind2 P Q a b := by
  induction P, Q using sturmSeq.induct with
  | case1 q => simp [varAt]
  | case2 p q hp ih =>
    rw [sturmSeq_cons hp] at h ⊢
    rcases eq_or_ne q 0 with rfl | hq
    · simp [varAt]
    have ht := ih fun r hr => h r (List.mem_cons_of_mem _ hr)
    obtain ⟨hpa, hpb⟩ := h p List.mem_cons_self
    obtain ⟨hqa, hqb⟩ := h q (List.mem_cons_of_mem _ (mem_sturmSeq_self hq))
    have key : ∀ t, p.eval t ≠ 0 → q.eval t ≠ 0 →
        varAt (p :: sturmSeq q (-p % q)) t = varAt (sturmSeq q (-p % q)) t +
          (if SignType.sign (p.eval t) = SignType.sign (q.eval t) then 0 else 1) := by
      intro t h1 h2
      rw [varAt, varAt, sturmSeq_cons hq]
      simp only [List.map_cons]
      rw [List.signVariations_cons_cons_of_ne_zero _ h1 h2]
    -- The Cauchy index of `(-p % q) / q` is minus that of `p / q`.
    have hind : ind2 q (-p % q) a b = -ind2 q p a b := by
      have : -p % q = -p + (-(-p / q)) * q := by
        rw [EuclideanDomain.mod_eq_sub_mul_div]; ring
      rw [this, ind2_add_mul hq, ind2_neg]
    have hinv := ind2_add_ind2 hp hq hab (by simp [hpa, hqa]) (by simp [hpb, hqb])
    have h2a := two_mul_ite_sign hpa hqa
    have h2b := two_mul_ite_sign hpb hqb
    rw [key a hpa hqa, key b hpb hqb]
    rw [hind] at ht
    simp only [eval_mul] at hinv
    push_cast at h2a h2b ⊢
    linear_combination ht + h2a - h2b - hinv

/-- **The Sturm–Tarski theorem on an interval.** If `a < b` are not roots of any polynomial in
the Sturm sequence of `P` and `P' Q` (this is stronger than the textbook hypothesis that `a`
and `b` are not roots of `P`, but suffices to derive `Adamar.sturm_tarski`), then the Tarski query of `Q` on the roots of `P` in
`(a, b)` is the difference of the numbers of sign variations of this sequence at `a` and `b`. -/
theorem sturm_tarski_interval {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X]) {a b : ℝ} (hab : a < b)
    (h : ∀ p ∈ sturmSeq P (derivative P * Q), p.eval a ≠ 0 ∧ p.eval b ≠ 0) :
    ∑ x ∈ rootsIn P a b, (SignType.sign (Q.eval x) : ℤ) =
      varAt (sturmSeq P (derivative P * Q)) a - varAt (sturmSeq P (derivative P * Q)) b := by
  have := two_mul_varAt_sub_varAt P (derivative P * Q) hab h
  rw [ind2_derivative_mul hP] at this
  omega

/-! ### Signs at infinity -/

/-- The sign of a non-zero polynomial at `+∞` is the sign of its leading coefficient. -/
lemma eventually_sign_eval_atTop {p : ℝ[X]} (hp : p ≠ 0) :
    ∀ᶠ t in Filter.atTop, SignType.sign (p.eval t) = SignType.sign p.leadingCoeff := by
  rcases eq_or_ne p.natDegree 0 with hd | hd
  · rw [eq_C_of_natDegree_eq_zero hd]
    simp
  have hdeg : 0 < p.degree := by
    rw [degree_eq_natDegree hp]; exact_mod_cast Nat.pos_of_ne_zero hd
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.2 hp) with hl | hl
  · have hdeg' : 0 < (-p).degree := by rwa [degree_neg]
    have := (tendsto_atTop_of_leadingCoeff_nonneg (-p) hdeg'
      (by rw [leadingCoeff_neg]; linarith)).eventually_gt_atTop 0
    filter_upwards [this] with t ht
    rw [eval_neg] at ht
    rw [sign_neg hl, sign_neg (by linarith)]
  · have := (tendsto_atTop_of_leadingCoeff_nonneg p hdeg hl.le).eventually_gt_atTop 0
    filter_upwards [this] with t ht
    rw [sign_pos hl, sign_pos ht]

/-- The sign of a non-zero polynomial at `-∞`. -/
lemma eventually_sign_eval_atBot {p : ℝ[X]} (hp : p ≠ 0) :
    ∀ᶠ t in Filter.atBot,
      SignType.sign (p.eval t) = SignType.sign ((-1) ^ p.natDegree * p.leadingCoeff) := by
  set q := p.comp (-X)
  have hnX : (-X : ℝ[X]).natDegree = 1 := by rw [natDegree_neg, natDegree_X]
  have hq : q ≠ 0 := by
    intro h
    apply hp
    have : q.comp (-X) = p := by simp [q, comp_assoc]
    rw [← this, h, zero_comp]
  have hlq : q.leadingCoeff = (-1) ^ p.natDegree * p.leadingCoeff := by
    rw [leadingCoeff_comp (by rw [hnX]; exact one_ne_zero), leadingCoeff_neg, leadingCoeff_X,
      mul_comm]
  have := Filter.tendsto_neg_atBot_atTop.eventually (eventually_sign_eval_atTop hq)
  filter_upwards [this] with t ht
  rw [← hlq, ← ht]
  simp [q, eval_comp]

/-- The number of sign variations of a list of polynomials at `+∞`. -/
def varPosInf (l : List ℝ[X]) : ℕ := (l.map leadingCoeff).signVariations

/-- The number of sign variations of a list of polynomials at `-∞`. -/
def varNegInf (l : List ℝ[X]) : ℕ :=
  (l.map fun p => (-1) ^ p.natDegree * p.leadingCoeff).signVariations

lemma eventually_varAt_atTop {l : List ℝ[X]} (hl : 0 ∉ l) :
    ∀ᶠ t in Filter.atTop, (∀ p ∈ l, p.eval t ≠ 0) ∧ varAt l t = varPosInf l := by
  classical
  have := (Filter.eventually_all_finset l.toFinset).2 fun p hp =>
    eventually_sign_eval_atTop (p := p) (fun h => hl (h ▸ List.mem_toFinset.1 hp))
  filter_upwards [this] with t ht
  simp only [List.mem_toFinset] at ht
  refine ⟨fun p hp h0 => ?_, ?_⟩
  · have := ht p hp
    rw [h0, sign_zero, eq_comm, sign_eq_zero_iff, leadingCoeff_eq_zero] at this
    exact hl (this ▸ hp)
  · refine List.signVariations_congr ?_
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun p hp => ht p hp

lemma eventually_varAt_atBot {l : List ℝ[X]} (hl : 0 ∉ l) :
    ∀ᶠ t in Filter.atBot, (∀ p ∈ l, p.eval t ≠ 0) ∧ varAt l t = varNegInf l := by
  classical
  have := (Filter.eventually_all_finset l.toFinset).2 fun p hp =>
    eventually_sign_eval_atBot (p := p) (fun h => hl (h ▸ List.mem_toFinset.1 hp))
  filter_upwards [this] with t ht
  simp only [List.mem_toFinset] at ht
  refine ⟨fun p hp h0 => ?_, ?_⟩
  · have := ht p hp
    rw [h0, sign_zero, eq_comm, sign_eq_zero_iff] at this
    have hp0 : p ≠ 0 := fun h => hl (h ▸ hp)
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.2 hp0) this
  · refine List.signVariations_congr ?_
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun p hp => ht p hp

/-! ### The Sturm–Tarski theorem -/

/-- **The Sturm–Tarski theorem** (*Algorithms in Real Algebraic Geometry*, Theorem 2.58). The
Tarski query `∑_{x, P(x) = 0} sign (Q x)` is the difference of the numbers of sign variations
of the Sturm sequence of `P` and `P' Q` at `-∞` and at `+∞`, which are read on the leading
coefficients. (For `P = 0`, both sides vanish, by Mathlib's conventions `roots 0 = 0` and
`sturmSeq 0 _ = []`.) -/
theorem sturm_tarski (P Q : ℝ[X]) :
    ∑ x ∈ P.roots.toFinset, (SignType.sign (Q.eval x) : ℤ) =
      varNegInf (sturmSeq P (derivative P * Q)) - varPosInf (sturmSeq P (derivative P * Q)) := by
  classical
  rcases eq_or_ne P 0 with rfl | hP
  · simp [varNegInf, varPosInf]
  set l := sturmSeq P (derivative P * Q)
  have hl : 0 ∉ l := zero_notMem_sturmSeq _ _
  set R := P.roots.toFinset
  -- Choose `a` below and `b` above all the roots of `P`, where the signs are those at infinity.
  have hbot := (eventually_varAt_atBot hl).and
    ((Filter.eventually_all_finset R).2 fun x _ => Filter.eventually_lt_atBot x)
  obtain ⟨a, ⟨ha, hva⟩, haR⟩ := hbot.exists
  have htop := ((eventually_varAt_atTop hl).and
    ((Filter.eventually_all_finset R).2 fun x _ => Filter.eventually_gt_atTop x)).and
    (Filter.eventually_gt_atTop a)
  obtain ⟨b, ⟨⟨hb, hvb⟩, hbR⟩, hab⟩ := htop.exists
  have hroots : rootsIn P a b = R := by
    ext x
    simp only [rootsIn, mem_filter]
    exact ⟨fun h => h.1, fun hx => ⟨hx, haR x hx, hbR x hx⟩⟩
  rw [← hroots, sturm_tarski_interval hP Q hab fun p hp => ⟨ha p hp, hb p hp⟩, hva, hvb]

/-- **Sturm's theorem**: the number of distinct real roots of `P` is the difference of the
numbers of sign variations of the Sturm sequence of `P` and `P'` at `-∞` and at `+∞`. -/
theorem sturm (P : ℝ[X]) :
    (P.roots.toFinset.card : ℤ) =
      varNegInf (sturmSeq P (derivative P)) - varPosInf (sturmSeq P (derivative P)) := by
  have := sturm_tarski P 1
  simp only [mul_one, eval_one, sign_one, SignType.coe_one, sum_const, nsmul_eq_mul,
    mul_one] at this
  exact this

end

end Adamar
