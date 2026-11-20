import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmAExpand
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

/- English proof (translation)
Introduce `I hI D S X A hX hA hAb c`. Establish `hfam : IsIntersectionFamily (I T.YBlk S.YIdx)` using `hI T.YBlk S.YIdx`. Establish `hXs : IsSmoothHerm X` using `hX.2.1`. Take `⟨Q, hQdef⟩ : ∃ Q : Polynomial ℝ, Q = ∑ j ∈ Finset.range (D + 1 + 1), Polynomial.C (((D + 1).choose j : ℝ) * ((1 / 2 : ℝ) ^ j * I T.YBlk S.YIdx S.YY (D + 1) (mix j X A)) * ((-1) ^ j + 1)) * Polynomial.X ^ j` from `⟨_, rfl⟩`. Establish `hQc : ∀ m, Q.coeff m = ((D + 1).choose m : ℝ) * ((1 / 2 : ℝ) ^ m * I T.YBlk S.YIdx S.YY (D + 1) (mix m X A)) * ((-1) ^ m + 1)`.

Introduce `m`. Rewrite using `[hQdef]`. Simplify using `only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with hm`.

Both sides reduce to the same expression. Rewrite using `[Nat.choose_eq_zero_of_lt (by simpa using hm)]`. Simplify using the standard rewrite rules. Establish `hQ : Q = tsgPoly D kappa (volPoly D fun j => (1 / 2 : ℝ) ^ j * ptsIntegral S.YY (pot (mix j X A : Fin D → HermLine S.YIdx)) (fun _ => 1))`. Use extensionality with `m`.

Rewrite using `[hQc]`. Take `⟨k, rfl | rfl⟩` from `Nat.even_or_odd' m`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Establish `h0 : I T.YBlk S.YIdx S.YY (D + 1) (mix 0 X A) = 0`. Establish `hm : (mix 0 X A : Fin (D + 1) → HermLine S.YIdx) = fun _ => A` using `funext fun i => by simp [mix]`.

Rewrite using `[hm]`. Conclude with `hP0 I hI D S A hA hAb`. Rewrite using `[mul_zero, h0, tsgPoly_coeff_zero]`. Simplify using the standard rewrite rules. Rewrite using `[tsgPoly_volPoly_coeff_even D _ kappa k hk, (even_two_mul k).neg_one_pow]`.

Distinguish the cases in `hkD : 2 * k ≤ D + 1`. Rewrite using `[hA' I hI D S X A hX hA hAb k hk hkD]`. Take `⟨i, hi⟩ : ∃ i, 2 * k = i + 1` from `⟨2 * k - 1, by omega⟩`. Rewrite using `[hi, Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Nat.choose_eq_zero_of_lt (by omega : D + 1 < 2 * k)]`. Simplify using the standard rewrite rules. Rewrite using `[tsgPoly_coeff_odd, (odd_two_mul_add_one k).neg_one_pow]`. Simplify using the standard rewrite rules. Rewrite using `[fam_lamLine_expand hfam S.arithYY hA hXs c, fam_lamLine_expand hfam S.arithYY hA hXs (-c), ← mul_add, ← hQ, hQdef]`.

Use `congr 1`. Simplify using `only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Int.cast_neg, neg_neg]`.

Rewrite using `[neg_div, neg_pow, div_eq_mul_one_div (c : ℝ) 2, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem TheoremA.proof (hP0 : ProjectivePointSetting.Statement) (hA' : PropAPrime.Statement) : TheoremA.Statement := by
  intro I hI D S X A hX hA hAb c
  have hfam : IsIntersectionFamily (I T.YBlk S.YIdx) := hI T.YBlk S.YIdx
  have hXs : IsSmoothHerm X := hX.2.1
  obtain ⟨Q, hQdef⟩ : ∃ Q : Polynomial ℝ, Q = ∑ j ∈ Finset.range (D + 1 + 1),
      Polynomial.C (((D + 1).choose j : ℝ) * ((1 / 2 : ℝ) ^ j * I T.YBlk S.YIdx S.YY (D + 1) (mix j X A)) *
        ((-1) ^ j + 1)) * Polynomial.X ^ j := ⟨_, rfl⟩
  have hQc : ∀ m, Q.coeff m = ((D + 1).choose m : ℝ) *
      ((1 / 2 : ℝ) ^ m * I T.YBlk S.YIdx S.YY (D + 1) (mix m X A)) * ((-1) ^ m + 1) := by
    intro m
    rw [hQdef]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · rw [Nat.choose_eq_zero_of_lt (by simpa using hm)]
      simp
  have hQ : Q = tsgPoly D kappa (volPoly D fun j =>
      (1 / 2 : ℝ) ^ j * ptsIntegral S.YY (pot (mix j X A : Fin D → HermLine S.YIdx)) (fun _ => 1)) := by
    ext m
    rw [hQc]
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · have h0 : I T.YBlk S.YIdx S.YY (D + 1) (mix 0 X A) = 0 := by
          have hm : (mix 0 X A : Fin (D + 1) → HermLine S.YIdx) = fun _ => A := funext fun i => by simp [mix]
          rw [hm]
          exact hP0 I hI D S A hA hAb
        rw [mul_zero, h0, tsgPoly_coeff_zero]
        simp
      · rw [tsgPoly_volPoly_coeff_even D _ kappa k hk, (even_two_mul k).neg_one_pow]
        by_cases hkD : 2 * k ≤ D + 1
        · rw [hA' I hI D S X A hX hA hAb k hk hkD]
          obtain ⟨i, hi⟩ : ∃ i, 2 * k = i + 1 := ⟨2 * k - 1, by omega⟩
          rw [hi, Nat.add_sub_cancel]
          ring
        · rw [Nat.choose_eq_zero_of_lt (by omega : D + 1 < 2 * k)]
          simp
    · rw [tsgPoly_coeff_odd, (odd_two_mul_add_one k).neg_one_pow]
      simp
  rw [fam_lamLine_expand hfam S.arithYY hA hXs c, fam_lamLine_expand hfam S.arithYY hA hXs (-c), ← mul_add,
    ← hQ, hQdef]
  congr 1
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Int.cast_neg, neg_neg]
  rw [neg_div, neg_pow, div_eq_mul_one_div (c : ℝ) 2, mul_pow]
  ring

end

end GroundTheory.Heights₂.Heights.Inter
