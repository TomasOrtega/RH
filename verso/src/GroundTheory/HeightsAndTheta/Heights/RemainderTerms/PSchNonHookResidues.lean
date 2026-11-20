import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

/- English proof (translation)
Establish `h` using `Finset.sum_range_reflect (fun i : ℕ => i) k`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => k - 1 - i) k, h, Finset.sum_range_id]`.
-/
theorem sum_fin_staircase (k : ℕ) : ∑ i : Fin k, (k - 1 - (i : ℕ)) = k * (k - 1) / 2 := by
  have h := Finset.sum_range_reflect (fun i : ℕ => i) k
  rw [Fin.sum_univ_eq_sum_range (fun i => k - 1 - i) k, h, Finset.sum_range_id]

/- English proof (translation)
Introduce `k nu hk hanti hsum hnot`. Use `push Not at hnot`. Take `⟨j, hj0, hj2⟩` from `hnot`. Establish `hk2 : 2 ≤ k` using `by have := j.isLt; omega`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Use `set l : Fin k → ℕ := fun i => nu i + (k - 1 - (i : ℕ)) with hl`. Establish `hinj : Function.Injective (fun i => l i % k)`. Introduce `a b hab`. Assume the negation of the conclusion as `hne`.

Conclude with `hcon a b hne hab`. Establish `hle : ∀ i, nu i ≤ k` using `fun i => hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Establish `hlt : ∀ i, l i < 2 * k`. Introduce `i`. Use `hle i` as an intermediate fact.

Use `i.isLt` as an intermediate fact. Simplify using `only [hl]`. Use linear arithmetic over natural numbers and integers. Establish `hcount` using `h1 k l hlt hinj`. Establish `hsumL : ∑ i, l i = k + k * (k - 1) / 2`.

Simplify using `only [hl, Finset.sum_add_distrib, hsum, sum_fin_staircase]`. Set `i0 : Fin k` to `⟨0, by omega⟩`. Set `i1 : Fin k` to `⟨1, by omega⟩`. Establish `h1le : nu j ≤ nu i1` using `hanti (show i1 ≤ j by rw [Fin.le_iff_val_le_val]; simp [i1]; omega)`. Establish `h0le : nu i1 ≤ nu i0` using `hanti (show i0 ≤ i1 by rw [Fin.le_iff_val_le_val]; simp [i0, i1])`.

Establish `hsub : ({i0, i1} : Finset (Fin k)) ⊆ univ.filter fun i => k ≤ l i`. Introduce `x hx`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hx`. Establish `hv0 : (i0 : ℕ) = 0` using `rfl`. Establish `hv1 : (i1 : ℕ) = 1` using `rfl`.

Apply the tactic sequence `rcases hx with rfl | rfl <;>`. Apply the tactic sequence `simp only [Finset.mem_filter, Finset.mem_univ, true_and, hl, hv0, hv1] <;> omega`. Establish `hcard : 2 ≤ (univ.filter fun i => k ≤ l i).card`. Use `Finset.card_le_card hsub` as an intermediate fact. Rewrite `this` using `[Finset.card_pair (by simp [i0, i1, Fin.ext_iff])]`. Then use the resulting hypothesis.

Establish `hmul` using `Nat.mul_le_mul_left k hcard`. Use linear arithmetic over natural numbers and integers.
-/
theorem SchNonHookResidues.proof (h1 : SchResidueCount.Statement) :
    SchNonHookResidues.Statement := by
  intro k nu hk hanti hsum hnot
  push Not at hnot
  obtain ⟨j, hj0, hj2⟩ := hnot
  have hk2 : 2 ≤ k := by have := j.isLt; omega
  by_contra hcon
  push Not at hcon
  set l : Fin k → ℕ := fun i => nu i + (k - 1 - (i : ℕ)) with hl
  have hinj : Function.Injective (fun i => l i % k) := by
    intro a b hab
    by_contra hne
    exact hcon a b hne hab
  have hle : ∀ i, nu i ≤ k := fun i =>
    hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hlt : ∀ i, l i < 2 * k := by
    intro i
    have := hle i
    have := i.isLt
    simp only [hl]
    omega
  have hcount := h1 k l hlt hinj
  have hsumL : ∑ i, l i = k + k * (k - 1) / 2 := by
    simp only [hl, Finset.sum_add_distrib, hsum, sum_fin_staircase]
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  have h1le : nu j ≤ nu i1 := hanti (show i1 ≤ j by rw [Fin.le_iff_val_le_val]; simp [i1]; omega)
  have h0le : nu i1 ≤ nu i0 := hanti (show i0 ≤ i1 by rw [Fin.le_iff_val_le_val]; simp [i0, i1])
  have hsub : ({i0, i1} : Finset (Fin k)) ⊆ univ.filter fun i => k ≤ l i := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hv0 : (i0 : ℕ) = 0 := rfl
    have hv1 : (i1 : ℕ) = 1 := rfl
    rcases hx with rfl | rfl <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hl, hv0, hv1] <;> omega
  have hcard : 2 ≤ (univ.filter fun i => k ≤ l i).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair (by simp [i0, i1, Fin.ext_iff])] at this
  have hmul := Nat.mul_le_mul_left k hcard
  omega

end GroundTheory.Heights₂.Heights.RestTerms
