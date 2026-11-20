import Formalism.SubspaceCounting.TopsChoiceSecondBound

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.G0

namespace TopsCount

def a (m : ℕ) (δ : ℝ) (j : ℕ) : ℝ := (m.choose j : ℝ) * δ ^ j * (1 - δ) ^ (m - j)

def A (m : ℕ) (δ : ℝ) (K : ℕ) : ℝ := ∑ j ∈ range K, a m δ j

/- English proof (translation)
Unfold `a`. Establish `: 0 ≤ 1 - δ` using `by linarith`. Check the signs of the components of the expression.
-/
lemma a_nonneg {m : ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j : ℕ) : 0 ≤ a m δ j := by
  unfold a
  have : 0 ≤ 1 - δ := by linarith
  positivity

/- English proof (translation)
Unfold `A`. Rewrite using `[sum_range_succ]`.
-/
lemma A_succ (m : ℕ) (δ : ℝ) (K : ℕ) : A m δ (K + 1) = A m δ K + a m δ K := by
  unfold A; rw [sum_range_succ]

/- English proof (translation)
Unfold `a`. Rewrite using `[Nat.choose_succ_succ', Nat.cast_add]`. Establish `e1 : m + 1 - (k + 1) = m - k` using `by omega`. Rewrite using `[e1]`. Break down `Nat.lt_or_ge k m with hk | hk` into its components or cases.

Establish `e2 : m - k = (m - (k + 1)) + 1` using `by omega`. Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Nat.choose_eq_zero_of_lt (by omega : m < k + 1)] push_cast; ring`.
-/
lemma pascal_term (m k : ℕ) (δ : ℝ) :
    ((m + 1).choose (k + 1) : ℝ) * δ ^ (k + 1) * (1 - δ) ^ (m + 1 - (k + 1)) =
      (1 - δ) * a m δ (k + 1) + δ * a m δ k := by
  unfold a
  rw [Nat.choose_succ_succ', Nat.cast_add]
  have e1 : m + 1 - (k + 1) = m - k := by omega
  rw [e1]
  rcases Nat.lt_or_ge k m with hk | hk
  · have e2 : m - k = (m - (k + 1)) + 1 := by omega
    rw [e2]; ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : m < k + 1)]
    push_cast; ring

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp [binLower, A]`. Consider the case `succ N ih`. Establish `hs : binLower (m + 1) δ (N + 1) = binLower (m + 1) δ N + ((m + 1).choose N : ℝ) * δ ^ N * (1 - δ) ^ (m + 1 - N)`. Unfold `binLower`.

Rewrite using `[sum_range_succ]`. Rewrite using `[hs, ih]`. Consider the cases of `N with`. Consider the case `zero`. Simplify using `[A, a]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `succ k`. Rewrite using `[show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega, A_succ m δ (k + 1), A_succ m δ k, pascal_term]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma binLower_eq (m : ℕ) (δ : ℝ) (N : ℕ) :
    binLower (m + 1) δ N = (1 - δ) * A m δ N + δ * A m δ (N - 1) := by
  induction N with
  | zero => simp [binLower, A]
  | succ N ih =>
    have hs : binLower (m + 1) δ (N + 1) =
        binLower (m + 1) δ N + ((m + 1).choose N : ℝ) * δ ^ N * (1 - δ) ^ (m + 1 - N) := by
      unfold binLower; rw [sum_range_succ]
    rw [hs, ih]
    cases N with
    | zero =>
      simp [A, a]
      ring
    | succ k =>
      rw [show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega,
        A_succ m δ (k + 1), A_succ m δ k, pascal_term]
      ring

/- English proof (translation)
Rewrite using `[← sum_filter]`. Unfold `A`. Apply `sum_subset` to reduce the goal to its premises. Introduce `j hj`. Simplify using `only [mem_filter] at hj`.

Conclude with `mem_range.2 hj.2`. Introduce `j hjK hj`. Simplify using `only [mem_filter, mem_range, not_and] at hj`. Establish `: m < j`. Assume the negation of the conclusion as `h`.

Conclude with `hj (by omega) (mem_range.1 hjK)`. Unfold `a`. Rewrite using `[Nat.choose_eq_zero_of_lt this]`. Simplify using the standard rewrite rules.
-/
lemma sum_ite_lt (m : ℕ) (δ : ℝ) (K : ℕ) :
    ∑ j ∈ range (m + 1), (if j < K then a m δ j else 0) = A m δ K := by
  rw [← sum_filter]
  unfold A
  apply sum_subset
  · intro j hj
    simp only [mem_filter] at hj
    exact mem_range.2 hj.2
  · intro j hjK hj
    simp only [mem_filter, mem_range, not_and] at hj
    have : m < j := by
      by_contra h
      exact hj (by omega) (mem_range.1 hjK)
    unfold a
    rw [Nat.choose_eq_zero_of_lt this]
    simp

/- English proof (translation)
Unfold `condProb`. Establish `h0 : (0 : ℕ) ∉ (range (m + 1)).erase 0` using `notMem_erase 0 _`. Establish `hr : range (m + 1) = insert 0 ((range (m + 1)).erase 0)` using `(insert_erase (by simp)).symm`. Rewrite using `[hr, sum_powerset_insert h0]`. Use `beta_reduce`.

Rewrite using `[Finset.sum_eq_zero, zero_add]`. Use `swap`. Introduce `t ht`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h, _⟩`.

Conclude with `h0 (mem_powerset.1 ht h)`. Rewrite using `[Finset.sum_congr rfl (g := fun t : Finset ℕ => (fun j : ℕ => if j < N - 1 then δ ^ j * (1 - δ) ^ (m - j) else 0) t.card)]`. Use `swap`. Introduce `t ht`. Establish `ht0 : (0 : ℕ) ∉ t` using `fun h => h0 (mem_powerset.1 ht h)`.

Rewrite using `[card_insert_of_notMem ht0]`. Use `beta_reduce`. Distinguish the cases in `hN : t.card + 1 < N`. Rewrite using `[if_pos ⟨mem_insert_self 0 t, hN⟩, if_pos (by omega), show t.card + 1 - 1 = t.card by omega, show m + 1 - (t.card + 1) = m - t.card by omega]`. Rewrite using `[if_neg (fun h => hN h.2), if_neg (by omega)]`.

Rewrite using `[sum_powerset_apply_card (fun j : ℕ => if j < N - 1 then δ ^ j * (1 - δ) ^ (m - j) else 0)]`. Establish `hcard : ((range (m + 1)).erase 0).card = m`. Rewrite using `[card_erase_of_mem (by simp), card_range]; rfl`. Rewrite using `[hcard, ← sum_ite_lt]`. Apply `sum_congr rfl` to reduce the goal to its premises.

Introduce `j _`. Rewrite using `[nsmul_eq_mul]`. Distinguish the cases in `hj : j < N - 1`. Rewrite using `[if_pos hj, if_pos hj]`. Unfold `a`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hj, if_neg hj, mul_zero]`.
-/
lemma condProb_card (m : ℕ) (δ : ℝ) (N : ℕ) :
    condProb (m + 1) δ (fun T => T.card < N) = A m δ (N - 1) := by
  classical
  unfold condProb
  have h0 : (0 : ℕ) ∉ (range (m + 1)).erase 0 := notMem_erase 0 _
  have hr : range (m + 1) = insert 0 ((range (m + 1)).erase 0) :=
    (insert_erase (by simp)).symm
  rw [hr, sum_powerset_insert h0]
  beta_reduce
  rw [Finset.sum_eq_zero, zero_add]
  swap
  · intro t ht
    rw [if_neg]
    rintro ⟨h, _⟩
    exact h0 (mem_powerset.1 ht h)
  rw [Finset.sum_congr rfl (g := fun t : Finset ℕ =>
    (fun j : ℕ => if j < N - 1 then δ ^ j * (1 - δ) ^ (m - j) else 0) t.card)]
  swap
  · intro t ht
    have ht0 : (0 : ℕ) ∉ t := fun h => h0 (mem_powerset.1 ht h)
    rw [card_insert_of_notMem ht0]
    beta_reduce
    by_cases hN : t.card + 1 < N
    · rw [if_pos ⟨mem_insert_self 0 t, hN⟩, if_pos (by omega),
        show t.card + 1 - 1 = t.card by omega, show m + 1 - (t.card + 1) = m - t.card by omega]
    · rw [if_neg (fun h => hN h.2), if_neg (by omega)]
  rw [sum_powerset_apply_card (fun j : ℕ => if j < N - 1 then δ ^ j * (1 - δ) ^ (m - j) else 0)]
  have hcard : ((range (m + 1)).erase 0).card = m := by
    rw [card_erase_of_mem (by simp), card_range]; rfl
  rw [hcard, ← sum_ite_lt]
  apply sum_congr rfl
  intro j _
  rw [nsmul_eq_mul]
  by_cases hj : j < N - 1
  · rw [if_pos hj, if_pos hj]; unfold a; ring
  · rw [if_neg hj, if_neg hj, mul_zero]

end TopsCount

open TopsCount in
/- English proof (translation)
Introduce `n δ N hn h0 h1`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Rewrite using `[condProb_card, binLower_eq]`. Establish `hA : A m δ (N - 1) ≤ A m δ N`. Unfold `A`.

Conclude with `sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (Nat.sub_le _ _)) (fun j _ _ => a_nonneg h0 h1 j)`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hA)]`.
-/
theorem tops_choice_count : SmallCardCondProbBound := by
  intro n δ N hn h0 h1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [condProb_card, binLower_eq]
  have hA : A m δ (N - 1) ≤ A m δ N := by
    unfold A
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (Nat.sub_le _ _))
      (fun j _ _ => a_nonneg h0 h1 j)
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hA)]

end Formalism.G0
