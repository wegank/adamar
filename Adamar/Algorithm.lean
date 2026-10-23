/-
Copyright (c) 2026 Weijia Wang. All rights reserved.
-/
import Adamar.TarskiQuery

/-!
# An incremental sign determination algorithm

This file is *not* part of the Coq development `signdet.v`. Its paper notes that the full
sign determination procedure is not formalized; here we formalize a simplified version of
Algorithm 10.96 (Sign Determination) of *Algorithms in Real Algebraic Geometry*, and prove its
correctness and its complexity in terms of calls to the Tarski query black box.

The algorithm takes as input a black box `oracle : (Fin n → Fin 3) → ℚ`, which is supposed
to return the Tarski query `TaQ(Q^α, Z)` on input `α`, and determines the realized sign
conditions `SIGN(Q, Z)` and the counts `c(σ, Z)` by adding the polynomials one at a time
(the first coordinate of tuples being the last polynomial added):

* with no polynomial, the only sign condition is realized iff `TaQ(1, Z) = #Z ≠ 0`;
* with polynomials `Q₀, Q₁, …, Qₙ`, we recursively determine the set `Σ'` of sign conditions
  realized by `Q₁, …, Qₙ`. The sign conditions realized by `Q₀, …, Qₙ` are among the
  *candidates* `{0, 1, -1} × Σ'`, so (by `Adamar.cnt_eq_sum_TaQ`) their counts are computed
  from the Tarski queries on the adapted family of the candidates. We keep the candidates with
  a non-zero count.

## Main results

* `Adamar.signDet_correct`: if the black box is correct on the products of at most
  `log₂ #Z + 1` of the polynomials `Q i` or `Q i ^ 2`, the algorithm returns `SIGN(Q, Z)` and
  the counts `c(σ, Z)`.
* `Adamar.signDet_congr`: the result only depends on the values of the black box on the set
  `Adamar.queries oracle` of queried products.
* `Adamar.card_queries_le`: under the correctness assumption, at most `1 + 2 n #Z` distinct
  queries are made (the bound `1 + 2 s r` of Algorithm 10.96 in the book).
-/

namespace Adamar

open Finset

section candidates

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}

/-- All the extensions of the elements of `S` (book: `{0, 1, -1} × S`). -/
def candidates (S : Finset (Fin n → X)) : Finset (Fin (n + 1) → X) :=
  univ.biUnion fun x => extset x S

variable {S : Finset (Fin n → X)}

@[simp] lemma mem_candidates {σ : Fin (n + 1) → X} : σ ∈ candidates S ↔ rem σ ∈ S := by
  simp [candidates, mem_extset]

lemma ext_mem_candidates {x : X} {r : Fin n → X} : ext x r ∈ candidates S ↔ r ∈ S := by
  simp

lemma card_candidates : (candidates S).card = Fintype.card X * S.card := by
  rw [candidates, card_biUnion fun x _ y _ hxy => disjoint_extset hxy S S]
  simp

lemma completions_candidates (r : Fin n → X) :
    completions (candidates S) r = if r ∈ S then univ else ∅ := by
  ext x
  split_ifs with h <;> simp [h]

lemma Xi_candidates {m : ℕ} (hm : m < Fintype.card X) : Xi m (candidates S) = S := by
  ext r
  rw [mem_Xi, completions_candidates]
  split_ifs with h <;> simp [h, hm]

end candidates

lemma adapt_candidates {k n : ℕ} (S : Finset (Fin n → Fin k)) :
    adapt (candidates S) = candidates (adapt S) := by
  ext σ
  rw [mem_adapt, mem_candidates, Xi_candidates (by simp)]

/-- The number of non-zero entries of a tuple. -/
def suppCard {k n : ℕ} [NeZero k] (α : Fin n → Fin k) : ℕ := #{i | α i ≠ 0}

lemma suppCard_ext_zero {k n : ℕ} [NeZero k] (α : Fin n → Fin k) :
    suppCard (ext 0 α) = suppCard α := by
  simp [suppCard, card_filter, Fin.sum_univ_succ]

lemma suppCard_succ {k n : ℕ} [NeZero k] (α : Fin (n + 1) → Fin k) :
    suppCard α = (if α 0 ≠ 0 then 1 else 0) + suppCard (rem α) := by
  rw [suppCard, suppCard, card_filter, card_filter, Fin.sum_univ_succ]
  rfl

lemma suppCard_le_succ {k n : ℕ} [NeZero k] (α : Fin (n + 1) → Fin k) :
    suppCard α ≤ suppCard (rem α) + 1 := by
  rw [suppCard_succ]
  split_ifs <;> omega

section algorithm

variable {n : ℕ}

/-- Solving the linear system `c · Mat(C, Ada(C)) = t` given by the Tarski queries `t` on
`Ada(C)`, for the counts `c` of the candidate sign conditions `C`. -/
noncomputable def solveCounts (C : Finset (Fin n → Fin 3)) (oracle : (Fin n → Fin 3) → ℚ)
    (σ : Fin n → Fin 3) : ℚ :=
  if h : σ ∈ C then ∑ α : adapt C, oracle α * adaptInv C α ⟨σ, h⟩ else 0

/-- The sign determination algorithm: computes the set of realized sign conditions from a
black box computing Tarski queries. -/
noncomputable def signDet : ∀ {n : ℕ}, ((Fin n → Fin 3) → ℚ) → Finset (Fin n → Fin 3)
  | 0, oracle => univ.filter fun σ => oracle σ ≠ 0
  | _ + 1, oracle =>
    let C := candidates (signDet fun α => oracle (ext 0 α))
    C.filter fun σ => solveCounts C oracle σ ≠ 0

/-- The counts computed by the sign determination algorithm. -/
noncomputable def countDet : ∀ {n : ℕ}, ((Fin n → Fin 3) → ℚ) → (Fin n → Fin 3) → ℚ
  | 0, oracle => oracle
  | _ + 1, oracle => solveCounts (candidates (signDet fun α => oracle (ext 0 α))) oracle

/-- The set of inputs on which the sign determination algorithm calls the black box. -/
noncomputable def queries : ∀ {n : ℕ}, ((Fin n → Fin 3) → ℚ) → Finset (Fin n → Fin 3)
  | 0, _ => univ
  | _ + 1, oracle =>
    (queries fun α => oracle (ext 0 α)).image (ext 0) ∪
      adapt (candidates (signDet fun α => oracle (ext 0 α)))

lemma signDet_succ (oracle : (Fin (n + 1) → Fin 3) → ℚ) :
    signDet oracle = (candidates (signDet fun α => oracle (ext 0 α))).filter
      fun σ => solveCounts (candidates (signDet fun α => oracle (ext 0 α))) oracle σ ≠ 0 :=
  rfl

lemma countDet_succ (oracle : (Fin (n + 1) → Fin 3) → ℚ) :
    countDet oracle = solveCounts (candidates (signDet fun α => oracle (ext 0 α))) oracle :=
  rfl

lemma queries_succ (oracle : (Fin (n + 1) → Fin 3) → ℚ) :
    queries oracle = (queries fun α => oracle (ext 0 α)).image (ext 0) ∪
      adapt (candidates (signDet fun α => oracle (ext 0 α))) :=
  rfl

/-- `solveCounts C oracle` only depends on the values of `oracle` on `adapt C`. -/
lemma solveCounts_congr (C : Finset (Fin n → Fin 3)) {o₁ o₂ : (Fin n → Fin 3) → ℚ}
    (h : ∀ α ∈ adapt C, o₁ α = o₂ α) : solveCounts C o₁ = solveCounts C o₂ := by
  ext σ
  unfold solveCounts
  split_ifs
  · exact sum_congr rfl fun α _ => by rw [h α α.2]
  · rfl

/-- The result of the algorithm only depends on the values of the black box on the queries.
Note that the queries themselves are computed adaptively. -/
theorem signDet_congr {o₁ o₂ : (Fin n → Fin 3) → ℚ} (h : ∀ α ∈ queries o₁, o₁ α = o₂ α) :
    signDet o₁ = signDet o₂ ∧ countDet o₁ = countDet o₂ ∧ queries o₁ = queries o₂ := by
  induction n with
  | zero =>
    have h' : o₁ = o₂ := funext fun α => h α (mem_univ α)
    subst h'
    exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    rw [queries_succ] at h
    obtain ⟨h1, -, h3⟩ := ih (o₁ := fun α => o₁ (ext 0 α)) (o₂ := fun α => o₂ (ext 0 α))
      fun α hα => h _ (mem_union_left _ (mem_image_of_mem _ hα))
    have hC := solveCounts_congr (candidates (signDet fun α => o₁ (ext 0 α)))
      fun α hα => h α (mem_union_right _ hα)
    refine ⟨?_, ?_, ?_⟩
    · rw [signDet_succ, signDet_succ, hC, h1]
    · rw [countDet_succ, countDet_succ, hC, h1]
    · rw [queries_succ, queries_succ, h1, h3]

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {P : Type*}

omit [LinearOrder R] [IsStrictOrderedRing R] in
lemma qpow_ext_zero (Q : Fin (n + 1) → P → R) (α : Fin n → Fin 3) :
    qpow Q (ext 0 α) = qpow (fun i => Q i.succ) α := by
  ext z
  simp [qpow, Fin.prod_univ_succ]

omit [IsStrictOrderedRing R] in
lemma signCond_succ (Q : Fin (n + 1) → P → R) (z : P) :
    signCond Q z = ext (signIdx (SignType.sign (Q 0 z))) (signCond (fun i => Q i.succ) z) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [signCond]

omit [IsStrictOrderedRing R] in
lemma SIGN_subset_candidates (Z : Finset P) (Q : Fin (n + 1) → P → R) :
    SIGN Z Q ⊆ candidates (SIGN Z fun i => Q i.succ) := by
  intro σ hσ
  obtain ⟨z, hz, rfl⟩ := (mem_SIGN Z Q).1 hσ
  rw [signCond_succ, ext_mem_candidates]
  exact (mem_SIGN _ _).2 ⟨z, hz, rfl⟩

/-- The black box is correct on all the products of at most `B` polynomials `Q i` or
`Q i ^ 2`. -/
def OracleCorrect (Z : Finset P) (Q : Fin n → P → R) (B : ℕ)
    (oracle : (Fin n → Fin 3) → ℚ) : Prop :=
  ∀ α, suppCard α ≤ B → oracle α = TaQ Z (qpow Q α)

omit [IsStrictOrderedRing R] in
lemma OracleCorrect.tail {Z : Finset P} {Q : Fin (n + 1) → P → R} {B : ℕ}
    {oracle : (Fin (n + 1) → Fin 3) → ℚ} (h : OracleCorrect Z Q B oracle) :
    OracleCorrect Z (fun i => Q i.succ) B fun α => oracle (ext 0 α) := fun α hα => by
  show oracle (ext 0 α) = _
  rw [h _ (by rwa [suppCard_ext_zero]), qpow_ext_zero]

/-- **Correctness of the sign determination algorithm.** If the black box computes the Tarski
queries of all the products of at most `log₂ #Z + 1` polynomials `Q i` or `Q i ^ 2`, then the
algorithm computes the set of realized sign conditions `SIGN(Q, Z)` and their counts, and
it only queries such products. -/
theorem signDet_correct (Z : Finset P) (Q : Fin n → P → R) (oracle : (Fin n → Fin 3) → ℚ)
    (h : OracleCorrect Z Q (Nat.log 2 Z.card + 1) oracle) :
    signDet oracle = SIGN Z Q ∧ (∀ σ, countDet oracle σ = cnt Z Q σ) ∧
      ∀ α ∈ queries oracle, suppCard α ≤ Nat.log 2 Z.card + 1 := by
  induction n with
  | zero =>
    have hcnt : ∀ σ, oracle σ = cnt Z Q σ := fun σ => by
      have hσ : ∀ z, signCond Q z = σ := fun z => Subsingleton.elim _ _
      rw [h σ (by simp [suppCard]), cnt, filter_true_of_mem fun z _ => hσ z]
      simp [TaQ, qpow]
    refine ⟨?_, hcnt, fun α _ => by simp [suppCard]⟩
    ext σ
    change σ ∈ univ.filter _ ↔ _
    rw [mem_filter, hcnt, Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero, cnt_pos_iff]
    exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
  | succ n ih =>
    set Q' : Fin n → P → R := fun i => Q i.succ
    obtain ⟨h1, -, h3⟩ := ih Q' _ h.tail
    set C := candidates (SIGN Z Q')
    have hC : SIGN Z Q ⊆ C := SIGN_subset_candidates Z Q
    -- The elements of `Ada(C)` are products of at most `log₂ #Z + 1` polynomials.
    have hsupp : ∀ α ∈ adapt C, suppCard α ≤ Nat.log 2 Z.card + 1 := fun α hα => by
      rw [adapt_candidates, mem_candidates] at hα
      refine (suppCard_le_succ α).trans (Nat.succ_le_succ ?_)
      exact (prop_10_84 _ _ hα).trans (Nat.log_mono_right (card_SIGN_le Z Q'))
    have hcnt : ∀ σ, solveCounts C oracle σ = cnt Z Q σ := fun σ => by
      unfold solveCounts
      split_ifs with hσ
      · rw [cnt_eq_sum_TaQ Z Q hC ⟨σ, hσ⟩]
        exact sum_congr rfl fun α _ => by rw [h α (hsupp α α.2)]
      · rw [eq_comm, Nat.cast_eq_zero, cnt_eq_zero_iff]
        exact fun h => hσ (hC h)
    refine ⟨?_, ?_, ?_⟩
    · rw [signDet_succ, h1]
      ext σ
      rw [mem_filter, hcnt, Nat.cast_ne_zero, ne_eq, cnt_eq_zero_iff, not_not]
      exact ⟨fun h => h.2, fun h => ⟨hC h, h⟩⟩
    · intro σ
      rw [countDet_succ, h1]
      exact hcnt σ
    · intro α hα
      rw [queries_succ, h1, mem_union, mem_image] at hα
      rcases hα with ⟨β, hβ, rfl⟩ | hα
      · rw [suppCard_ext_zero]
        exact h3 β hβ
      · exact hsupp α hα

/-- The queries contain the adapted family of the realized sign conditions. -/
lemma adapt_SIGN_subset_queries (Z : Finset P) (Q : Fin n → P → R)
    (oracle : (Fin n → Fin 3) → ℚ) (h : OracleCorrect Z Q (Nat.log 2 Z.card + 1) oracle) :
    adapt (SIGN Z Q) ⊆ queries oracle := by
  cases n with
  | zero => exact fun _ _ => mem_univ _
  | succ n =>
    obtain ⟨h1, -, -⟩ := signDet_correct Z (fun i => Q i.succ) _ h.tail
    rw [queries_succ, h1]
    exact (adapt_mono (SIGN_subset_candidates Z Q)).trans subset_union_right

/-- **Number of calls to the black box.** Under the correctness assumption, the algorithm
makes at most `1 + 2 n #Z` distinct queries. -/
theorem card_queries_le (Z : Finset P) (Q : Fin n → P → R) (oracle : (Fin n → Fin 3) → ℚ)
    (h : OracleCorrect Z Q (Nat.log 2 Z.card + 1) oracle) :
    (queries oracle).card ≤ 1 + 2 * n * Z.card := by
  induction n with
  | zero => simp [queries]
  | succ n ih =>
    set Q' : Fin n → P → R := fun i => Q i.succ
    set o' : (Fin n → Fin 3) → ℚ := fun α => oracle (ext 0 α)
    have ih' := ih Q' o' h.tail
    obtain ⟨h1, -, -⟩ := signDet_correct Z Q' o' h.tail
    set S' := SIGN Z Q'
    -- The queries of the recursive call contain `Ada(S')`.
    have hsub : adapt S' ⊆ queries o' := adapt_SIGN_subset_queries Z Q' o' h.tail
    -- Among the new queries `Ada(C) = {0, 1, 2} × Ada(S')`, those starting with `0` are old.
    have hnew : adapt (candidates (signDet o')) \ (queries o').image (ext 0) ⊆
        (adapt (candidates S')).filter fun σ => σ 0 ≠ 0 := by
      intro σ hσ
      rw [mem_sdiff, h1] at hσ
      refine mem_filter.2 ⟨hσ.1, fun h0 => hσ.2 (mem_image.2 ⟨rem σ, ?_, ?_⟩)⟩
      · rw [adapt_candidates, mem_candidates] at hσ
        exact hsub hσ.1
      · rw [← h0, ext_rem]
    have hcard : ((adapt (candidates S')).filter fun σ => σ 0 ≠ 0).card ≤ 2 * Z.card := by
      rw [adapt_candidates]
      have : (candidates (adapt S')).filter (fun σ => σ 0 ≠ 0) =
          extset 1 (adapt S') ∪ extset 2 (adapt S') := by
        ext σ
        simp only [mem_filter, mem_candidates, mem_union, mem_extset]
        constructor
        · rintro ⟨hr, h0⟩
          have : σ 0 = 1 ∨ σ 0 = 2 := by omega
          tauto
        · rintro (⟨h0, hr⟩ | ⟨h0, hr⟩) <;> exact ⟨hr, by simp [h0]⟩
      rw [this]
      refine (card_union_le _ _).trans ?_
      rw [card_extset, card_extset, card_adapt]
      have : S'.card ≤ Z.card := card_SIGN_le Z Q'
      omega
    rw [queries_succ, ← union_sdiff_self_eq_union]
    refine (card_union_le _ _).trans ?_
    rw [card_image_of_injective _ (ext_injective 0)]
    have := card_le_card hnew
    nlinarith

/-- **Correctness from the queries only.** It suffices that the black box answers correctly
the queries actually made by the algorithm: then the algorithm computes `SIGN(Q, Z)` and the
counts, with at most `1 + 2 n #Z` queries, each a product of at most `log₂ #Z + 1`
polynomials `Q i` or `Q i ^ 2`. -/
theorem signDet_correct_of_queries (Z : Finset P) (Q : Fin n → P → R)
    (oracle : (Fin n → Fin 3) → ℚ)
    (h : ∀ α ∈ queries oracle, oracle α = TaQ Z (qpow Q α)) :
    signDet oracle = SIGN Z Q ∧ (∀ σ, countDet oracle σ = cnt Z Q σ) ∧
      (queries oracle).card ≤ 1 + 2 * n * Z.card ∧
      ∀ α ∈ queries oracle, suppCard α ≤ Nat.log 2 Z.card + 1 := by
  set o : (Fin n → Fin 3) → ℚ := fun α => TaQ Z (qpow Q α)
  have ho : OracleCorrect Z Q (Nat.log 2 Z.card + 1) o := fun _ _ => rfl
  obtain ⟨h1, h2, h3⟩ := signDet_congr (o₁ := oracle) (o₂ := o) h
  obtain ⟨c1, c2, c3⟩ := signDet_correct Z Q o ho
  refine ⟨h1.trans c1, fun σ => by rw [h2, c2], ?_, ?_⟩
  · rw [h3]
    exact card_queries_le Z Q o ho
  · rw [h3]
    exact c3

end algorithm

end Adamar
