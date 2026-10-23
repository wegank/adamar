/-
Copyright (c) 2026 Weijia Wang. All rights reserved.
-/
import Adamar.Effective
import Adamar.Executable
import Adamar.PolyList

/-!
# Executable sign determination at the real roots of a rational polynomial

We compute the Tarski queries of the Sturm–Tarski theorem on the executable polynomials of
`Adamar.PolyL` (`Adamar.sturmQueryL`), and feed them to the executable sign determination
algorithm `Adamar.signDetExec`. The result is a verified program which, given the
coefficients of rational polynomials `P` and `Q₀, …, Q_{n-1}`, computes the sign
conditions realized by the `Q i` at the *real* roots of `P` (which are in general irrational)
together with the numbers of roots realizing them (`Adamar.signDetExec_sturmQueryL`).
-/

namespace Adamar

open Polynomial PolyL

noncomputable section

/-- The real polynomial with rational coefficient list `l`. -/
def toReal (l : List ℚ) : ℝ[X] := (toPoly l).map (algebraMap ℚ ℝ)

lemma sturmSeq_map (P Q : ℚ[X]) :
    (sturmSeq P Q).map (map (algebraMap ℚ ℝ)) =
      sturmSeq (P.map (algebraMap ℚ ℝ)) (Q.map (algebraMap ℚ ℝ)) := by
  induction P, Q using sturmSeq.induct with
  | case1 q => simp
  | case2 p q hp ih =>
    rw [sturmSeq_cons hp, sturmSeq_cons ((Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).2 hp),
      List.map_cons, ih, Polynomial.map_mod, Polynomial.map_neg]

end

/-! ### Executable Tarski queries -/

/-- The leading coefficient of a coefficient list. -/
def lcL (l : List ℚ) : ℚ := (trimL l).getLastD 0

/-- The degree of a coefficient list. -/
def degL (l : List ℚ) : ℕ := (trimL l).length - 1

lemma lcL_eq (l : List ℚ) : lcL l = (toPoly l).leadingCoeff := getLastD_trimL l

lemma degL_eq (l : List ℚ) : degL l = (toPoly l).natDegree := by
  rw [degL, length_trimL]
  split_ifs with h
  · simp [h]
  · omega

/-- The number of sign variations at `+∞` of a list of coefficient lists. -/
def varPosInfL (L : List (List ℚ)) : ℕ := (L.map lcL).signVariations

/-- The number of sign variations at `-∞` of a list of coefficient lists. -/
def varNegInfL (L : List (List ℚ)) : ℕ := (L.map fun l => (-1) ^ degL l * lcL l).signVariations

/-- The Tarski query of `q` on the real roots of `p`, computed by the Sturm–Tarski theorem. -/
def sturmQueryL (p q : List ℚ) : ℤ :=
  varNegInfL (sturmL p (mulL (derivL p) q)) - varPosInfL (sturmL p (mulL (derivL p) q))

lemma sign_ratCast (x : ℚ) : SignType.sign ((x : ℝ)) = SignType.sign x := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [sign_neg h, sign_neg (by exact_mod_cast h)]
  · simp
  · rw [sign_pos h, sign_pos (by exact_mod_cast h)]

/-- The executable Tarski query agrees with `Adamar.sturmQuery` over `ℝ`. -/
theorem sturmQueryL_eq (p q : List ℚ) : sturmQueryL p q = sturmQuery (toReal p) (toReal q) := by
  set f := algebraMap ℚ ℝ
  set L := sturmL p (mulL (derivL p) q)
  have hS : sturmSeq (toReal p) (derivative (toReal p) * toReal q) =
      (L.map toPoly).map (map f) := by
    rw [map_sturmL, sturmSeq_map, toReal, toReal, derivative_map, toPoly_mulL, toPoly_derivL,
      Polynomial.map_mul]
  have hpos : varPosInf (sturmSeq (toReal p) (derivative (toReal p) * toReal q)) =
      varPosInfL L := by
    rw [hS, varPosInf, varPosInfL, List.map_map, List.map_map]
    refine List.signVariations_congr ?_
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun l _ => ?_
    simp [leadingCoeff_map, lcL_eq, f, sign_ratCast]
  have hneg : varNegInf (sturmSeq (toReal p) (derivative (toReal p) * toReal q)) =
      varNegInfL L := by
    rw [hS, varNegInf, varNegInfL, List.map_map, List.map_map]
    refine List.signVariations_congr ?_
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun l _ => ?_
    have : ((-1 : ℝ) ^ (toPoly l).natDegree * ((toPoly l).leadingCoeff : ℝ)) =
        (((-1) ^ (toPoly l).natDegree * (toPoly l).leadingCoeff : ℚ) : ℝ) := by push_cast; ring
    simp only [Function.comp_apply, leadingCoeff_map, natDegree_map, lcL_eq, degL_eq, f,
      eq_ratCast, this, sign_ratCast]
  rw [sturmQuery, sturmQueryL, hpos, hneg]

lemma toReal_one : toReal [1] = 1 := by simp [toReal]

/-- **Counting real roots by computation.** The number of distinct real roots of the rational
polynomial with coefficient list `p` is computed by `sturmQueryL p [1]` (Sturm's theorem). -/
theorem card_roots_eq_sturmQueryL (p : List ℚ) :
    ((toReal p).roots.toFinset.card : ℤ) = sturmQueryL p [1] := by
  rw [sturmQueryL_eq, toReal_one, sturmQuery]
  rw [mul_one]
  simpa using sturm (toReal p)

/-! ### Products -/

variable {n : ℕ}

/-- The product `∏ i, qs i ^ α i` of coefficient lists. -/
def polyPowL (qs : Fin n → List ℚ) (α : Fin n → Fin 3) : List ℚ :=
  (List.finRange n).foldr (fun i acc => mulL (powL (qs i) (α i)) acc) [1]

lemma toPoly_foldr (qs : Fin n → List ℚ) (α : Fin n → Fin 3) (l : List (Fin n)) :
    toPoly (l.foldr (fun i acc => mulL (powL (qs i) (α i)) acc) [1]) =
      (l.map fun i => toPoly (qs i) ^ (α i : ℕ)).prod := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

lemma toReal_polyPowL (qs : Fin n → List ℚ) (α : Fin n → Fin 3) :
    toReal (polyPowL qs α) = polyPow (fun i => toReal (qs i)) α := by
  rw [toReal, polyPowL, toPoly_foldr, ← List.ofFn_eq_map, Fin.prod_ofFn, polyPow,
    Polynomial.map_prod]
  simp [toReal]

/-! ### The verified program -/

/-- **Executable sign determination at the real roots of a rational polynomial.** For rational
coefficient lists `p` and `qs`, the executable algorithm
`Adamar.signDetExec`, run with the executable Sturm–Tarski queries `Adamar.sturmQueryL`,
computes the sign conditions realized by the `qs i` at the real roots of `p`, and the numbers
of real roots realizing them. -/
theorem signDetExec_sturmQueryL (p : List ℚ) (qs : Fin n → List ℚ) :
    let oracle := fun α => (sturmQueryL p (polyPowL qs α) : ℚ)
    let Z := (toReal p).roots.toFinset
    signDetExec oracle = SIGN Z (fun i x => (toReal (qs i)).eval x) ∧
      ∀ σ, countDetExec oracle σ = cnt Z (fun i x => (toReal (qs i)).eval x) σ := by
  intro oracle Z
  have ho : oracle = fun α => (sturmQuery (toReal p) (polyPow (fun i => toReal (qs i)) α) : ℚ) := by
    funext α
    simp only [oracle, sturmQueryL_eq, toReal_polyPowL]
  obtain ⟨h1, h2, -⟩ := signDet_sturm (toReal p) (fun i => toReal (qs i))
  rw [ho, signDetExec_eq, countDetExec_eq]
  exact ⟨h1, h2⟩

end Adamar
