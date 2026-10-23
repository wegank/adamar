/-
Copyright (c) 2026 Weijia Wang. All rights reserved.
Portions copyright (c) 2014 Cyril Cohen (Coq development `signdet.v`), used under the MIT
license as described in the file LICENSE.
-/
import Mathlib

/-!
# Extensions and restrictions of tuples

This file is the Lean counterpart of the section `Ext` of `signdet.v`.

For a finite type `X`, the elements of `X ^ n` are represented as functions `Fin n → X`.
We define

* `Adamar.ext x r`: the tuple `r : Fin n → X` extended by `x` at the beginning;
* `Adamar.rem s`: the tuple `s : Fin (n + 1) → X` with its first element removed
  (the inverse of `ext`);
* `Adamar.extset x R`: the image of a set `R` of tuples under `ext x`;
* `Adamar.completions S r` (Coq: `compl`): the set of `x` such that `ext x r ∈ S`;
* `Adamar.Xi m S`: the set of tuples `r` that have at least `m + 1` completions in `S`.

In the book *Algorithms in Real Algebraic Geometry* (Basu, Pollack, Roy), `Xi m S` is the
set `Ξ(m)` of Notation 10.76, except that the book splits along the *last* polynomial while we
split along the *first* coordinate.
-/

namespace Adamar

open Finset

variable {X : Type*} {n : ℕ}

/-- Extension of `r` with one element `x` at the beginning. -/
def ext (x : X) (r : Fin n → X) : Fin (n + 1) → X := Fin.cons x r

/-- Removal of the first element of `s`, the inverse of `ext`. -/
def rem (s : Fin (n + 1) → X) : Fin n → X := Fin.tail s

@[simp] lemma ext_zero (x : X) (r : Fin n → X) : ext x r 0 = x := Fin.cons_zero _ _

@[simp] lemma ext_succ (x : X) (r : Fin n → X) (i : Fin n) : ext x r i.succ = r i :=
  Fin.cons_succ _ _ _

@[simp] lemma rem_apply (s : Fin (n + 1) → X) (i : Fin n) : rem s i = s i.succ := rfl

/-- Coq: `extK`. -/
@[simp] lemma rem_ext (x : X) (r : Fin n → X) : rem (ext x r) = r := Fin.tail_cons _ _

/-- Coq: `remK`. -/
@[simp] lemma ext_rem (s : Fin (n + 1) → X) : ext (s 0) (rem s) = s := Fin.cons_self_tail s

/-- Coq: `eq_ext`. -/
lemma ext_inj {x x' : X} {r r' : Fin n → X} : ext x r = ext x' r' ↔ x = x' ∧ r = r' :=
  Fin.cons_inj

lemma ext_injective (x : X) : Function.Injective (ext x : (Fin n → X) → Fin (n + 1) → X) :=
  fun _ _ h => (ext_inj.1 h).2

lemma ext_left_injective (r : Fin n → X) : Function.Injective (fun x : X => ext x r) :=
  fun _ _ h => (ext_inj.1 h).1

variable [DecidableEq X]

/-- Extension of a set `R` of tuples with one element `x` at the beginning. -/
def extset (x : X) (R : Finset (Fin n → X)) : Finset (Fin (n + 1) → X) := R.image (ext x)

section extset

variable {R R' : Finset (Fin n → X)} {s : Fin (n + 1) → X} {r : Fin n → X} {x : X}

/-- Coq: `card_extset`. -/
@[simp] lemma card_extset (x : X) (R : Finset (Fin n → X)) : (extset x R).card = R.card :=
  card_image_of_injective _ (ext_injective x)

/-- Coq: `mem_extset`. -/
lemma mem_extset : s ∈ extset x R ↔ s 0 = x ∧ rem s ∈ R := by
  constructor
  · rintro hs
    obtain ⟨r, hr, rfl⟩ := mem_image.1 hs
    simpa using hr
  · rintro ⟨h0, hR⟩
    exact mem_image.2 ⟨rem s, hR, by rw [← h0, ext_rem]⟩

/-- Coq: `mem_extset_r`. -/
@[simp] lemma ext_mem_extset : ext x r ∈ extset x R ↔ r ∈ R := by
  simp [mem_extset]

/-- Coq: `extset0`. -/
@[simp] lemma extset_empty (x : X) : extset x (∅ : Finset (Fin n → X)) = ∅ := by
  simp [extset]

/-- Coq: `subset_extset`. -/
@[simp] lemma extset_subset_extset_iff : extset x R ⊆ extset x R' ↔ R ⊆ R' := by
  constructor
  · intro h r hr
    simpa using h (ext_mem_extset.2 hr)
  · exact image_subset_image

/-- Extensions by different elements are disjoint. -/
lemma disjoint_extset {x y : X} (hxy : x ≠ y) (R R' : Finset (Fin n → X)) :
    Disjoint (extset x R) (extset y R') := by
  rw [disjoint_left]
  intro s hx hy
  exact hxy ((mem_extset.1 hx).1.symm.trans (mem_extset.1 hy).1)

end extset

variable [Fintype X]

/-- The set of possible completions of `r` by `x` in `S` (Coq: `compl`). -/
def completions (S : Finset (Fin (n + 1) → X)) (r : Fin n → X) : Finset X :=
  univ.filter fun x => ext x r ∈ S

/-- The set of tuples having at least `m + 1` completions in `S`. -/
def Xi (m : ℕ) (S : Finset (Fin (n + 1) → X)) : Finset (Fin n → X) :=
  univ.filter fun r => m < (completions S r).card

variable {S S' : Finset (Fin (n + 1) → X)} {R R' : Finset (Fin n → X)}
  {s : Fin (n + 1) → X} {r : Fin n → X} {x : X} {m p : ℕ}

/-- Coq: `ext_in`. -/
@[simp] lemma mem_completions : x ∈ completions S r ↔ ext x r ∈ S := by
  simp [completions]

@[simp] lemma mem_Xi : r ∈ Xi m S ↔ m < (completions S r).card := by
  simp [Xi]

/-- Coq: `compl0`. -/
@[simp] lemma completions_empty (r : Fin n → X) :
    completions (∅ : Finset (Fin (n + 1) → X)) r = ∅ := by
  ext; simp

/-- Coq: `ord0_in_compl`. -/
lemma zero_mem_completions_rem (hs : s ∈ S) : s 0 ∈ completions S (rem s) := by
  simpa using hs

/-- Coq: `compl_rem_neq0`. -/
lemma completions_rem_nonempty (hs : s ∈ S) : (completions S (rem s)).Nonempty :=
  ⟨_, zero_mem_completions_rem hs⟩

/-- Coq: `rem_inW`. -/
lemma rem_mem_Xi_zero (hs : s ∈ S) : rem s ∈ Xi 0 S := by
  simpa [card_pos] using completions_rem_nonempty hs

/-- `Xi 0` is a left inverse of `extset x` (Coq: `extsetK`). -/
@[simp] lemma Xi_zero_extset (x : X) (R : Finset (Fin n → X)) : Xi 0 (extset x R) = R := by
  ext r
  simp only [mem_Xi, card_pos, Finset.Nonempty, mem_completions, mem_extset, ext_zero, rem_ext]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨x, rfl, h⟩⟩

/-- Coq: `subset_compl`. -/
lemma completions_mono (h : S ⊆ S') (r : Fin n → X) : completions S r ⊆ completions S' r :=
  fun _ hx => mem_completions.2 (h (mem_completions.1 hx))

/-- Coq: `subset_Xi`. -/
lemma Xi_mono (m : ℕ) (h : S ⊆ S') : Xi m S ⊆ Xi m S' := fun r hr => by
  simp only [mem_Xi] at hr ⊢
  exact hr.trans_le (card_le_card (completions_mono h r))

/-- Coq: `leq_Xi`. -/
lemma Xi_anti (S : Finset (Fin (n + 1) → X)) (h : p ≤ m) : Xi m S ⊆ Xi p S := fun r hr => by
  simp only [mem_Xi] at hr ⊢
  omega

/-- Coq: `Xi0`. -/
@[simp] lemma Xi_empty (m : ℕ) : Xi m (∅ : Finset (Fin (n + 1) → X)) = ∅ := by
  ext; simp

/-- Coq: `Xi1_eq0`. -/
@[simp] lemma Xi_zero_eq_empty : Xi 0 S = ∅ ↔ S = ∅ := by
  constructor
  · intro h
    by_contra hS
    obtain ⟨s, hs⟩ := nonempty_iff_ne_empty.2 hS
    simpa [h] using rem_mem_Xi_zero hs
  · rintro rfl
    exact Xi_empty 0

lemma not_mem_Xi : r ∉ Xi m S ↔ (completions S r).card ≤ m := by
  simp

/-- Summing over a set of tuples of length `n + 1` amounts to summing over the possible
restrictions and then over their completions. -/
lemma sum_eq_sum_completions {M : Type*} [AddCommMonoid M] (S : Finset (Fin (n + 1) → X))
    (f : (Fin (n + 1) → X) → M) :
    ∑ s ∈ S, f s = ∑ r, ∑ x ∈ completions S r, f (ext x r) := by
  rw [← sum_fiberwise S rem f]
  refine sum_congr rfl fun r _ => ?_
  refine sum_nbij' (fun s => s 0) (fun x => ext x r) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [mem_filter] at hs
    simpa [← hs.2] using hs.1
  · intro x hx
    simpa using hx
  · intro s hs
    simp only [mem_filter] at hs
    simp [← hs.2]
  · intro x _
    simp
  · intro s hs
    simp only [mem_filter] at hs
    simp [← hs.2]

/-- The sizes of the sets `Xi m S`, for `m` ranging over `0, …, #X - 1`, add up to `#S`. -/
lemma sum_card_Xi (S : Finset (Fin (n + 1) → X)) :
    ∑ m ∈ range (Fintype.card X), (Xi m S).card = S.card := by
  have hS : S.card = ∑ r, (completions S r).card := by
    rw [card_eq_sum_ones, sum_eq_sum_completions]
    simp
  rw [hS]
  simp only [Xi, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun r _ => ?_
  have hle : (completions S r).card ≤ Fintype.card X := card_le_univ _
  rw [← card_filter]
  conv_rhs => rw [← card_range (completions S r).card]
  congr 1
  ext m
  simp only [mem_filter, mem_range]
  omega

end Adamar
