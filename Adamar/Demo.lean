/-
Copyright (c) 2026 Weijia Wang. All rights reserved.
-/
import Adamar.EffectiveExec

/-!
# Running the sign determination algorithm

We run the executable sign determination algorithm `Adamar.signDetExec` on concrete examples,
where the black box computes Tarski queries directly on a finite set of rational points.
By `Adamar.signDetExec_correct`, the output is the set of realized sign conditions with their
counts; we also compare it with the direct computation of `Adamar.SIGN`.
-/

namespace Adamar.Demo

open Adamar

/-- Displays a sign condition with the signs `0, 1, -1`. -/
def showSign {n : ℕ} (σ : Fin n → Fin 3) : List ℤ :=
  List.ofFn fun i => if σ i = 0 then 0 else if σ i = 1 then 1 else -1

/-- Runs the algorithm with the black box `α ↦ TaQ(Q^α, Z)`, and lists the realized sign
conditions with their counts. -/
def run {n : ℕ} (Z : Finset ℚ) (Q : Fin n → ℚ → ℚ) : List (List ℤ × ℚ) :=
  let oracle := fun α => (TaQ Z (qpow Q α) : ℚ)
  (enumList (signDetExec oracle)).map fun σ => (showSign σ, countDetExec oracle σ)

/-! ### Three polynomials on six points -/

/-- Six points. -/
def Z₁ : Finset ℚ := {-2, -1, 0, 1/2, 1, 3}

/-- The polynomials `x`, `x - 1` and `x² - 2`. -/
def Q₁ : Fin 3 → ℚ → ℚ := ![fun x => x, fun x => x - 1, fun x => x ^ 2 - 2]

/--
info: [([0, -1, -1], 1), ([1, 0, -1], 1), ([1, 1, 1], 1), ([1, -1, -1], 1), ([-1, -1, 1], 1), ([-1, -1, -1], 1)]
-/
#guard_msgs in
#eval run Z₁ Q₁

/-- info: true -/
#guard_msgs in
#eval signDetExec (fun α => (TaQ Z₁ (qpow Q₁ α) : ℚ)) == SIGN Z₁ Q₁

/-! ### Five polynomials on twenty points -/

/-- The points `-5, -4.5, …, 4.5`. -/
def Z₂ : Finset ℚ := (Finset.range 20).image fun k : ℕ => ((k : ℚ) / 2 - 5)

/-- The polynomials `x`, `x - 1`, `x² - 2`, `x³ - x` and `x + 3`. -/
def Q₂ : Fin 5 → ℚ → ℚ :=
  ![fun x => x, fun x => x - 1, fun x => x ^ 2 - 2, fun x => x ^ 3 - x, fun x => x + 3]

/--
info: [([0, -1, -1, 0, 1], 1), ([1, 0, -1, 0, 1], 1), ([1, 1, 1, 1, 1], 7), ([1, -1, -1, -1, 1], 1), ([-1, -1, 1, -1, 0], 1),
  ([-1, -1, 1, -1, 1], 3), ([-1, -1, 1, -1, -1], 4), ([-1, -1, -1, 0, 1], 1), ([-1, -1, -1, 1, 1], 1)]
-/
#guard_msgs in
#eval run Z₂ Q₂

/-! ### Real roots of rational polynomials, from the coefficients only

Here the Tarski queries are not computed on given points but by the Sturm–Tarski theorem
(`Adamar.sturmQueryL`) from the coefficient lists (constant coefficient first). By
`Adamar.signDetExec_sturmQueryL`, the output is the list of sign conditions realized at the
*real* roots of `p`, with the number of roots realizing each of them. -/

open Adamar.PolyL in
/-- Sign determination at the real roots of `p` for the polynomials `qs`. -/
def runRoots {n : ℕ} (p : List ℚ) (qs : Fin n → List ℚ) : List (List ℤ × ℚ) :=
  let oracle := fun α => (sturmQueryL p (polyPowL qs α) : ℚ)
  (enumList (signDetExec oracle)).map fun σ => (showSign σ, countDetExec oracle σ)

/-- `x³ - 3x + 1` has exactly three real roots: a theorem, proved by computing a Sturm sequence
in the kernel. -/
theorem card_roots_example : (toReal [1, -3, 0, 1]).roots.toFinset.card = 3 := by
  have h := card_roots_eq_sturmQueryL [1, -3, 0, 1]
  rw [show sturmQueryL [1, -3, 0, 1] [1] = 3 by decide +kernel] at h
  exact_mod_cast h

/- The signs of `x`, `x² - 2` and `x - 1` at the three (irrational) real roots
`≈ -1.879, 0.347, 1.532` of `x³ - 3x + 1`. -/
/-- info: [([1, 1, 1], 1), ([1, -1, -1], 1), ([-1, 1, -1], 1)] -/
#guard_msgs in
#eval runRoots [1, -3, 0, 1] ![[0, 1], [-2, 0, 1], [-1, 1]]

/-- The sign conditions realized by `x`, `x² - 2` and `x - 1` at the real roots of
`x³ - 3x + 1` (signs `0, 1, -1` encoded as `0, 1, 2`): `(+,+,+)`, `(+,-,-)` and `(-,+,-)`.
This is a theorem about real numbers, proved by running the verified program in the kernel. -/
theorem signs_example :
    SIGN (toReal [1, -3, 0, 1]).roots.toFinset
        (fun i x => (toReal (![[0, 1], [-2, 0, 1], [-1, 1]] i)).eval x) =
      {![1, 1, 1], ![1, 2, 2], ![2, 1, 2]} := by
  rw [← (signDetExec_sturmQueryL [1, -3, 0, 1] ![[0, 1], [-2, 0, 1], [-1, 1]]).1]
  decide +kernel

/- The signs of `x`, `x² - 2` and `x³ - x - 1` at the roots `-2, -1, 0, 1, 2` of
`x⁵ - 5x³ + 4x`. -/
/--
info: [([0, -1, -1], 1), ([1, 1, 1], 1), ([1, -1, -1], 1), ([-1, 1, -1], 1), ([-1, -1, -1], 1)]
-/
#guard_msgs in
#eval runRoots [0, 4, 0, -5, 0, 1] ![[0, 1], [-2, 0, 1], [-1, -1, 0, 1]]

end Adamar.Demo
