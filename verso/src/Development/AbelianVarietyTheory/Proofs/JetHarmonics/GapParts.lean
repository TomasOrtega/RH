import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces

set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

/- English proof (translation)
Unfold `gap`. Distinguish the cases in `h1 : k + 1 < r`. Use `h k (k + 1) (by omega) h1` as an intermediate fact. Rewrite using `[if_pos (show 1 ≤ k + 1 ∧ k + 1 ≤ r by omega), if_pos h1, if_pos (show k < r by omega), Nat.add_sub_cancel]`. Use linear arithmetic over natural numbers and integers.

Distinguish the cases in `h2 : k < r`. Rewrite using `[if_pos (show 1 ≤ k + 1 ∧ k + 1 ≤ r by omega), if_neg h1, if_pos h2, Nat.add_sub_cancel]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg (show ¬ (1 ≤ k + 1 ∧ k + 1 ≤ r) by omega), if_neg h1, if_neg h2]`.
-/
private theorem gap_step (r : ℕ) (a : ℕ → ℕ) (h : ∀ i j, i ≤ j → j < r → a j ≤ a i) (k : ℕ) :
    gap r a (k + 1) + (if k + 1 < r then a (k + 1) else 0) = (if k < r then a k else 0) := by
  unfold gap
  by_cases h1 : k + 1 < r
  · have := h k (k + 1) (by omega) h1
    rw [if_pos (show 1 ≤ k + 1 ∧ k + 1 ≤ r by omega), if_pos h1, if_pos (show k < r by omega),
      Nat.add_sub_cancel]
    omega
  · by_cases h2 : k < r
    · rw [if_pos (show 1 ≤ k + 1 ∧ k + 1 ≤ r by omega), if_neg h1, if_pos h2, Nat.add_sub_cancel]
      omega
    · rw [if_neg (show ¬ (1 ≤ k + 1 ∧ k + 1 ≤ r) by omega), if_neg h1, if_neg h2]

/- English proof (translation)
Proceed by induction on `K, hK using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ K hK ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega), add_assoc, gap_step r a h K, ih]`.
-/
private theorem gap_tele (r : ℕ) (a : ℕ → ℕ) (h : ∀ i j, i ≤ j → j < r → a j ≤ a i) (i K : ℕ)
    (hK : i ≤ K) :
    ∑ k ∈ Finset.Icc (i + 1) K, gap r a k + (if K < r then a K else 0)
      = (if i < r then a i else 0) := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_assoc, gap_step r a h K, ih]

/- English proof (translation)
Proceed by induction on `K with`. Consider the case `zero => simp`. Consider the case `succ K ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega), add_assoc, ← mul_add, gap_step r a h K, Finset.sum_range_succ, ← ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem gap_parts (r : ℕ) (a : ℕ → ℕ) (h : ∀ i j, i ≤ j → j < r → a j ≤ a i) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, k * gap r a k + K * (if K < r then a K else 0)
      = ∑ i ∈ Finset.range K, (if i < r then a i else 0) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_assoc, ← mul_add, gap_step r a h K,
      Finset.sum_range_succ, ← ih]
    ring

/- English proof (translation)
Introduce `r a h`. Use `⟨fun k hk => ?_, fun K hK => ⟨fun i hi => ?_, ?_⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Conclude with `hk (by unfold gap; rw [if_neg hc])`. Use `gap_tele r a h i K (by omega)` as an intermediate fact.

Rewrite `this` using `[if_neg (show ¬ K < r by omega), if_pos hi, add_zero]`. Conclude with `this`. Use `gap_parts r a h K` as an intermediate fact. Rewrite `this` using `[if_neg (show ¬ K < r by omega), mul_zero, add_zero]`. Rewrite using `[this, Fin.sum_univ_eq_sum_range a r, ← Finset.sum_filter]`.

Use `congr 1`. Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.
-/
theorem gap_sums : ∀ (r : ℕ) (a : ℕ → ℕ), (∀ i j, i ≤ j → j < r → a j ≤ a i) → (∀ k, gap r a k ≠ 0 → 1 ≤ k ∧ k ≤ r) ∧ ∀ K, r ≤ K → (∀ i, i < r → ∑ k ∈ Finset.Icc (i + 1) K, gap r a k = a i) ∧ ∑ k ∈ Finset.Icc 1 K, k * gap r a k = ∑ i : Fin r, a i := by
  intro r a h
  refine ⟨fun k hk => ?_, fun K hK => ⟨fun i hi => ?_, ?_⟩⟩
  · by_contra hc
    exact hk (by unfold gap; rw [if_neg hc])
  · have := gap_tele r a h i K (by omega)
    rw [if_neg (show ¬ K < r by omega), if_pos hi, add_zero] at this
    exact this
  · have := gap_parts r a h K
    rw [if_neg (show ¬ K < r by omega), mul_zero, add_zero] at this
    rw [this, Fin.sum_univ_eq_sum_range a r, ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega

end GlobalTheory.RowAt
