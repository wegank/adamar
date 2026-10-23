/-
Copyright (c) 2026 Weijia Wang. All rights reserved.
-/
import Adamar.Algorithm
import Adamar.SturmTarski

/-!
# Effective sign determination at the roots of a real polynomial

We combine the Sturm–Tarski theorem (`Adamar.sturm_tarski`) with the sign determination of
`Adamar.TarskiQuery` and `Adamar.Algorithm`. For `P : ℝ[X]` and polynomials
`Q₀, …, Q_{n-1}`, the realized sign conditions of the `Q i` at the roots of `P` and the numbers
of roots realizing them are computed from numbers of sign variations of Sturm sequences, i.e.
from the coefficients of the polynomials only.
-/

namespace Adamar

open Polynomial Finset

noncomputable section

/-- The Tarski query of `Q` on the roots of `P`, as computed by the Sturm–Tarski theorem from the
Sturm sequence of `P` and `P' Q`. -/
def sturmQuery (P Q : ℝ[X]) : ℤ :=
  varNegInf (sturmSeq P (derivative P * Q)) - varPosInf (sturmSeq P (derivative P * Q))

/-- The univariate Tarski query is computed by the Sturm–Tarski theorem. -/
theorem TaQPoly_eq_sturmQuery (P Q : ℝ[X]) : TaQPoly P Q = sturmQuery P Q :=
  sturm_tarski P Q

variable {n : ℕ}

/-- **Sign determination from Sturm sequences.** For `P` and `Q₀, …, Q_{n-1}`, with
`Z = Zer(P)` and `S = SIGN(Q, Z)`, the number of roots of `P` realizing `σ ∈ S` is a fixed linear
combination of the `#S ≤ deg P` numbers `sturmQuery P (Q^α)`, `α ∈ Ada(S)`, each of which
involves a product of at most `log₂ (deg P)` polynomials `Q i` or `Q i ^ 2`. -/
theorem sign_determination_sturm (P : ℝ[X]) (Q : Fin n → ℝ[X]) :
    let Z := P.roots.toFinset
    let S := SIGN Z fun i x => (Q i).eval x
    S.card ≤ P.natDegree ∧ (adapt S).card = S.card ∧
    (∀ α ∈ adapt S, #{i | α i ≠ 0} ≤ Nat.log 2 P.natDegree) ∧
    ∀ σ : S, (cnt Z (fun i x => (Q i).eval x) σ : ℚ) =
      ∑ α : adapt S, (sturmQuery P (polyPow Q α) : ℚ) * adaptInv S α σ := by
  intro Z S
  obtain ⟨h1, h2, h3, h4⟩ := sign_determination_roots (P := P) Q
  refine ⟨h1, h2, h3, fun σ => ?_⟩
  rw [h4 σ]
  simp_rw [TaQPoly_eq_sturmQuery]
  rfl

/-- **The complete sign determination procedure.** Running the algorithm `Adamar.signDet` with
the Tarski queries computed by Sturm sequences gives the sign conditions realized by
`Q₀, …, Q_{n-1}` at the roots of `P`, the numbers of roots realizing them, and makes at
most `1 + 2 n #Zer(P)` calls to `sturmQuery`, each on a product of at most
`log₂ #Zer(P) + 1` polynomials `Q i` or `Q i ^ 2`. -/
theorem signDet_sturm (P : ℝ[X]) (Q : Fin n → ℝ[X]) :
    let oracle := fun α => (sturmQuery P (polyPow Q α) : ℚ)
    let Z := P.roots.toFinset
    signDet oracle = SIGN Z (fun i x => (Q i).eval x) ∧
      (∀ σ, countDet oracle σ = cnt Z (fun i x => (Q i).eval x) σ) ∧
      (queries oracle).card ≤ 1 + 2 * n * Z.card ∧
      ∀ α ∈ queries oracle, suppCard α ≤ Nat.log 2 Z.card + 1 := by
  intro oracle Z
  have h : ∀ α ∈ queries oracle,
      oracle α = TaQ Z (qpow (fun i x => (Q i).eval x) α) := fun α _ => by
    simp only [oracle, ← TaQPoly_eq_sturmQuery, TaQPoly_polyPow]
    rfl
  exact signDet_correct_of_queries Z _ oracle h

end

end Adamar
