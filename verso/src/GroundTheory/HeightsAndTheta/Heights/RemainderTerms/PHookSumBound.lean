import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

/- English proof (translation)
Use `set g : ℕ → ℕ := fun j => if h : j < r then nu ⟨j, h⟩ else 0 with hg`. Establish `hgnu : ∀ i : Fin r, g i = nu i` using `fun i => by simp [hg, i.isLt]`. Establish `hsumg : ∑ j ∈ range r, g j = k`. Rewrite using `[← Fin.sum_univ_eq_sum_range]`. Simplify using `only [hgnu]`.

Conclude with `hsum`. Establish `hr : 0 < r`. Break down `Nat.eq_zero_or_pos r with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using `at hsumg`.

Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `hanti_g : ∀ i j, i ≤ j → g j ≤ g i`. Introduce `i j hij`. Distinguish the cases in `hj : j < r`.

Establish `hi : i < r` using `lt_of_le_of_lt hij hj`. Simplify using `only [hg, dif_pos hj, dif_pos hi]`. Conclude with `hanti (show (⟨i, hi⟩ : Fin r) ≤ ⟨j, hj⟩ from hij)`. Simplify using `[hg, dif_neg hj]`. Establish `hle1 : ∀ j, 1 ≤ j → g j ≤ 1`.

Introduce `j hj`. Distinguish the cases in `h : j < r`. Simplify using `only [hg, dif_pos h]`. Conclude with `hhook ⟨j, h⟩ (by simp only; omega)`. Simplify using `[hg, dif_neg h]`.

Establish `hsplit : g 0 + ∑ j ∈ Ico 1 r, g j = k`. Rewrite using `[← Finset.sum_eq_sum_Ico_succ_bot hr, ← Finset.range_eq_Ico]`. Conclude with `hsumg`. Use `set t := ∑ j ∈ Ico 1 r, g j with ht`. Establish `hrow : ∀ i, 1 ≤ i → i < r → g i = if i ≤ t then 1 else 0`.

Introduce `i hi1 hir`. Break down `Nat.le_one_iff_eq_zero_or_eq_one.mp (hle1 i hi1) with h0 | h1` into its components or cases. Establish `hz : ∀ j ∈ Ico i r, g j = 0` using `fun j hj => by`. Use `hanti_g i j (mem_Ico.mp hj).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hti : t ≤ i - 1`. Rewrite using `[ht, ← Finset.sum_Ico_consecutive g hi1 hir.le, Finset.sum_eq_zero hz, add_zero]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h0, if_neg (by omega)]`. Establish `ho : ∀ j ∈ Ico 1 (i + 1), g j = 1` using `fun j hj => by`.

Establish `h2` using `hanti_g j i (by have := (mem_Ico.mp hj).2; omega)`. Establish `h3` using `hle1 j (mem_Ico.mp hj).1`. Use linear arithmetic over natural numbers and integers. Establish `hit : i ≤ t`. Rewrite using `[ht, ← Finset.sum_Ico_consecutive g (show 1 ≤ i + 1 by omega) (show i + 1 ≤ r by omega), Finset.sum_congr rfl ho]`.

Simplify using the standard rewrite rules. Rewrite using `[h1, if_pos hit]`. Establish `htr : t < r`. Establish `: t ≤ r - 1`. Combine the equalities or inequalities in the displayed calculation.

Use linear arithmetic over natural numbers and integers. Establish `hg0 : 1 ≤ g 0`. Assume the negation of the conclusion as `h`. Establish `hz : ∀ j, g j = 0` using `fun j => by`. Use `hanti_g 0 j (Nat.zero_le j)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using `[hz] at hsumg`. Use linear arithmetic over natural numbers and integers. Use `⟨t, htr, by omega, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Rewrite using `[← hgnu i]`. Unfold `hookShape`. Distinguish the cases in `hi0 : (i : ℕ) = 0`. Rewrite using `[if_pos hi0, hi0]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_neg hi0, hrow i (by omega) i.isLt]`.
-/
theorem exists_hookShape_of_isHook {r k : ℕ} (hk : 1 ≤ k) (nu : Fin r → ℕ) (hanti : Antitone nu)
    (hsum : ∑ i, nu i = k) (hhook : ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) :
    ∃ l, l < r ∧ l < k ∧ nu = hookShape r k l := by
  set g : ℕ → ℕ := fun j => if h : j < r then nu ⟨j, h⟩ else 0 with hg
  have hgnu : ∀ i : Fin r, g i = nu i := fun i => by simp [hg, i.isLt]
  have hsumg : ∑ j ∈ range r, g j = k := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [hgnu]
    exact hsum
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      simp at hsumg
      omega
    · exact h
  have hanti_g : ∀ i j, i ≤ j → g j ≤ g i := by
    intro i j hij
    by_cases hj : j < r
    · have hi : i < r := lt_of_le_of_lt hij hj
      simp only [hg, dif_pos hj, dif_pos hi]
      exact hanti (show (⟨i, hi⟩ : Fin r) ≤ ⟨j, hj⟩ from hij)
    · simp [hg, dif_neg hj]
  have hle1 : ∀ j, 1 ≤ j → g j ≤ 1 := by
    intro j hj
    by_cases h : j < r
    · simp only [hg, dif_pos h]
      exact hhook ⟨j, h⟩ (by simp only; omega)
    · simp [hg, dif_neg h]
  have hsplit : g 0 + ∑ j ∈ Ico 1 r, g j = k := by
    rw [← Finset.sum_eq_sum_Ico_succ_bot hr, ← Finset.range_eq_Ico]
    exact hsumg
  set t := ∑ j ∈ Ico 1 r, g j with ht
  have hrow : ∀ i, 1 ≤ i → i < r → g i = if i ≤ t then 1 else 0 := by
    intro i hi1 hir
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hle1 i hi1) with h0 | h1
    · have hz : ∀ j ∈ Ico i r, g j = 0 := fun j hj => by
        have := hanti_g i j (mem_Ico.mp hj).1
        omega
      have hti : t ≤ i - 1 := by
        rw [ht, ← Finset.sum_Ico_consecutive g hi1 hir.le, Finset.sum_eq_zero hz, add_zero]
        calc ∑ j ∈ Ico 1 i, g j ≤ ∑ j ∈ Ico 1 i, 1 :=
              Finset.sum_le_sum fun j hj => hle1 j (mem_Ico.mp hj).1
          _ = i - 1 := by simp
      rw [h0, if_neg (by omega)]
    · have ho : ∀ j ∈ Ico 1 (i + 1), g j = 1 := fun j hj => by
        have h2 := hanti_g j i (by have := (mem_Ico.mp hj).2; omega)
        have h3 := hle1 j (mem_Ico.mp hj).1
        omega
      have hit : i ≤ t := by
        rw [ht, ← Finset.sum_Ico_consecutive g (show 1 ≤ i + 1 by omega)
          (show i + 1 ≤ r by omega), Finset.sum_congr rfl ho]
        simp
      rw [h1, if_pos hit]
  have htr : t < r := by
    have : t ≤ r - 1 := by
      calc t ≤ ∑ j ∈ Ico 1 r, 1 := Finset.sum_le_sum fun j hj => hle1 j (mem_Ico.mp hj).1
        _ = r - 1 := by simp
    omega
  have hg0 : 1 ≤ g 0 := by
    by_contra h
    have hz : ∀ j, g j = 0 := fun j => by
      have := hanti_g 0 j (Nat.zero_le j)
      omega
    simp [hz] at hsumg
    omega
  refine ⟨t, htr, by omega, ?_⟩
  funext i
  rw [← hgnu i]
  unfold hookShape
  by_cases hi0 : (i : ℕ) = 0
  · rw [if_pos hi0, hi0]
    omega
  · rw [if_neg hi0, hrow i (by omega) i.isLt]

/- English proof (translation)
Introduce `r a k b hk hb`. Establish `hB0 : (0 : ℚ) ≤ (Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a)`. Check the signs of the components of the expression. Establish `hterm : ∀ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1), |b nu| ≤ ((Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a)) * (numStandardTable nu : ℚ)`. Introduce `nu hnu`.

Establish `hmem` using `(Finset.mem_filter.mp hnu).1`. Establish `h` using `Finset.mem_filter.mp hmem`. Establish `hsum : ∑ i, nu i = k` using `Finset.Nat.mem_antidiagonalTuple.mp h.1`. Establish `hc` using `hC r a nu (fun i j hij => h.2 i j hij)`. Rewrite `hc` using `[hsum]`.

Combine the equalities or inequalities in the displayed calculation. Establish `himg : (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) ⊆ (range (min r k)).image (hookShape r k)`. Introduce `nu hnu`. Take `⟨hmem, hhook⟩` from `Finset.mem_filter.mp hnu`. Establish `h` using `Finset.mem_filter.mp hmem`.

Take `⟨l, hlr, hlk, rfl⟩` from `exists_hookShape_of_isHook hk nu (fun i j hij => h.2 i j hij) (Finset.Nat.mem_antidiagonalTuple.mp h.1) hhook`. Conclude with `Finset.mem_image.mpr ⟨l, Finset.mem_range.mpr (lt_min hlr hlk), rfl⟩`. Use `(Finset.sum_le_sum hterm).trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum]`. Establish `hhooks : ∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1), (numStandardTable nu : ℚ) ≤ 2 ^ (k - 1)`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Establish `hl'` using `lt_min_iff.mp (Finset.mem_range.mp hl)`. Rewrite using `[hH r k l hl'.2 hl'.1]`. Use `_ ≤ ∑ l ∈ range k, ((k - 1).choose l : ℚ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_right _ _)) fun _ _ _ => by positivity`.

Use `_ = 2 ^ (k - 1) := by`. Take `⟨n, rfl⟩ : ∃ n, k = n + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[Nat.add_sub_cancel]`. Conclude with `Nat.sum_range_choose n` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation.
-/
theorem HookSumBound.proof (hC : LemmaC.Statement) (hH : HookTableauCount.Statement) :
    HookSumBound.Statement := by
  intro r a k b hk hb
  have hB0 : (0 : ℚ) ≤ (Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a) := by
    positivity
  have hterm : ∀ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
      |b nu| ≤ ((Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a)) *
        (numStandardTable nu : ℚ) := by
    intro nu hnu
    have hmem := (Finset.mem_filter.mp hnu).1
    have h := Finset.mem_filter.mp hmem
    have hsum : ∑ i, nu i = k := Finset.Nat.mem_antidiagonalTuple.mp h.1
    have hc := hC r a nu (fun i j hij => h.2 i j hij)
    rw [hsum] at hc
    calc |b nu| ≤ numStandardTable (fun i => a + nu i) := hb nu hmem
      _ ≤ _ := by exact_mod_cast hc
  have himg : (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) ⊆
      (range (min r k)).image (hookShape r k) := by
    intro nu hnu
    obtain ⟨hmem, hhook⟩ := Finset.mem_filter.mp hnu
    have h := Finset.mem_filter.mp hmem
    obtain ⟨l, hlr, hlk, rfl⟩ := exists_hookShape_of_isHook hk nu (fun i j hij => h.2 i j hij)
      (Finset.Nat.mem_antidiagonalTuple.mp h.1) hhook
    exact Finset.mem_image.mpr ⟨l, Finset.mem_range.mpr (lt_min hlr hlk), rfl⟩
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hhooks : ∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
      (numStandardTable nu : ℚ) ≤ 2 ^ (k - 1) := by
    calc _ ≤ ∑ nu ∈ (range (min r k)).image (hookShape r k), (numStandardTable nu : ℚ) :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => by positivity
      _ ≤ ∑ l ∈ range (min r k), (numStandardTable (hookShape r k l) : ℚ) :=
          Finset.sum_image_le_of_nonneg fun _ _ => by positivity
      _ = ∑ l ∈ range (min r k), ((k - 1).choose l : ℚ) := by
          refine Finset.sum_congr rfl fun l hl => ?_
          have hl' := lt_min_iff.mp (Finset.mem_range.mp hl)
          rw [hH r k l hl'.2 hl'.1]
      _ ≤ ∑ l ∈ range k, ((k - 1).choose l : ℚ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_right _ _))
            fun _ _ _ => by positivity
      _ = 2 ^ (k - 1) := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          rw [Nat.add_sub_cancel]
          exact_mod_cast Nat.sum_range_choose n
  calc _ ≤ ((Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a)) * 2 ^ (k - 1) :=
        mul_le_mul_of_nonneg_left hhooks hB0
    _ = _ := by ring

end GroundTheory.Heights₂.Heights.RestTerms
