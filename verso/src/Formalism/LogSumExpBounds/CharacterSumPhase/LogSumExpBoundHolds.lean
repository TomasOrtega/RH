import Formalism.LogSumExpBounds.NuclearBound

namespace Formalism.NuclearRankWeightBounds.P

open Finset

/- English proof (translation)
Break down `le_or_gt 0 z with h0 | h0` into its components or cases. Use `Real.quadratic_le_exp_of_nonneg h0` as an intermediate fact. Use polynomial arithmetic with `[sq_nonneg z]`. Establish `h` using `Real.exp_bound hz (n := 5) (by norm_num)`. Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h`.

Evaluate the numerical expressions using `at h`. Establish `h2` using `(abs_le.mp h).1`. Establish `ha : |z| = -z` using `abs_of_neg h0`. Rewrite `h2`, `hz` using `[ha]`. Establish `hz1 : -1 ≤ z` using `by linarith`.

Use polynomial arithmetic with `[sq_nonneg z, mul_nonneg (mul_nonneg (sq_nonneg z) (by linarith : (0:ℝ) ≤ z + 1)) (by linarith : (0:ℝ) ≤ -z), pow_two_nonneg (z ^ 2), mul_nonneg (sq_nonneg z) (by linarith : (0:ℝ) ≤ z + 1), mul_nonneg (mul_nonneg (sq_nonneg z) (sq_nonneg z)) (by linarith : (0:ℝ) ≤ z + 1)]`.
-/
lemma exp_ge_quad {z : ℝ} (hz : |z| ≤ 1) : 1 + z + z ^ 2 / 3 ≤ Real.exp z := by
  rcases le_or_gt 0 z with h0 | h0
  · have := Real.quadratic_le_exp_of_nonneg h0
    nlinarith [sq_nonneg z]
  · have h := Real.exp_bound hz (n := 5) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    have h2 := (abs_le.mp h).1
    have ha : |z| = -z := abs_of_neg h0
    rw [ha] at h2 hz
    have hz1 : -1 ≤ z := by linarith
    nlinarith [sq_nonneg z, mul_nonneg (mul_nonneg (sq_nonneg z) (by linarith : (0:ℝ) ≤ z + 1)) (by linarith : (0:ℝ) ≤ -z),
      pow_two_nonneg (z ^ 2), mul_nonneg (sq_nonneg z) (by linarith : (0:ℝ) ≤ z + 1),
      mul_nonneg (mul_nonneg (sq_nonneg z) (sq_nonneg z)) (by linarith : (0:ℝ) ≤ z + 1)]

/- English proof (translation)
Introduce `ι _ w y M hw hw1 hmean hy`. Establish `hne : Nonempty ι`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nonempty_iff]`. Simplify using `at hw1`.

Take `⟨j0⟩` from `hne`. Establish `hM0 : 0 ≤ M` using `le_trans (abs_nonneg _) (hy j0)`. Use `set S := ∑ j, w j * Real.exp (y j) with hS`. Use `set V := ∑ j, w j * y j ^ 2 with hV`. Establish `hV0 : 0 ≤ V` using `Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (sq_nonneg _))`.

Break down `eq_or_lt_of_le hM0 with hM | hM` into its components or cases. Substitute `hM` using the available equality. Establish `hy0 : ∀ j, y j = 0` using `fun j => abs_nonpos_iff.mp (hy j)`. Establish `: S = 1` using `by simp [hS, hy0, hw1]`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Use `set t := min 1 M⁻¹ with ht`. Establish `ht0 : 0 < t` using `lt_min one_pos (inv_pos.mpr hM)`. Establish `ht1 : t ≤ 1` using `min_le_left _ _`. Establish `htM : t * M ≤ 1`.

Combine the equalities or inequalities in the displayed calculation. Establish `hty : ∀ j, |t * y j| ≤ 1`. Introduce `j`. Rewrite using `[abs_mul, abs_of_pos ht0]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hVM : V ≤ M ^ 2`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `j _`. Apply `mul_le_mul_of_nonneg_left _ (hw j)` to reduce the goal to its premises.

Rewrite using `[← sq_abs]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) (hy j) 2`. Use `_ = M ^ 2 := by rw [← Finset.sum_mul, hw1, one_mul]`. Use `set T := ∑ j, w j * Real.exp (t * y j) with hT`. Establish `hT1 : 1 + t ^ 2 * V / 3 ≤ T`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_add, Finset.sum_add_distrib, mul_one, hw1]`. Establish `e1 : ∑ j, w j * (t * y j) = t * ∑ j, w j * y j`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)`. Establish `e2 : ∑ j, w j * ((t * y j) ^ 2 / 3) = t ^ 2 * V / 3`.

Rewrite using `[hV, Finset.mul_sum, Finset.sum_div]`. Conclude with `Finset.sum_congr rfl (fun j _ => by ring)`. Rewrite using `[e1, e2, hmean]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ T := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (exp_ge_quad (hty j)) (hw j))`.

Establish `hu : t ^ 2 * V ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Establish `: 0 ≤ t * M` using `mul_nonneg ht0.le hM.le`. Use the polynomial consequences of the given equalities and inequalities. Establish `hTpos : 0 < T`.

Establish `: 0 ≤ t ^ 2 * V` using `mul_nonneg (sq_nonneg _) hV0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogT : t ^ 2 * V / 4 ≤ Real.log T` using `by set u := t ^ 2 * V / 3 with hu'`. Establish `hu0 : 0 ≤ u` using `by positivity`. Establish `hlog1 : 1 - (1 + u)⁻¹ ≤ Real.log (1 + u)` using `Real.one_sub_inv_le_log_of_pos (by linarith)`.

Establish `hmono : Real.log (1 + u) ≤ Real.log T` using `Real.log_le_log (by linarith) hT1`. Establish `: t ^ 2 * V / 4 ≤ 1 - (1 + u)⁻¹`. Rewrite using `[show 1 - (1 + u)⁻¹ = u / (1 + u) by field_simp; ring]`. Rewrite using `[le_div_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hJ : T ^ (1 / t) ≤ S`. Establish `h` using `Real.rpow_arith_mean_le_arith_mean_rpow (s := Finset.univ) w (fun j => Real.exp (t * y j)) (fun j _ => hw j) hw1 (fun j _ => (Real.exp_pos _).le) (p := 1 / t) (by rw [le_div_iff₀ ht0]; linarith)`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations.

Rewrite using `[← Real.exp_mul]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts. Establish `hlogJ : (1 / t) * Real.log T ≤ Real.log S`. Rewrite using `[← Real.log_rpow hTpos]`.

Conclude with `Real.log_le_log (Real.rpow_pos_of_pos hTpos _) hJ`. Establish `key : t * V / 4 ≤ (1 / t) * Real.log T`. Rewrite using `[div_mul_eq_mul_div, one_mul, le_div_iff₀ ht0]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_sum_exp_bound_holds : Formalism.NuclearRankWeightBounds.D.LogSumExp := by
  intro ι _ w y M hw hw1 hmean hy
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hw1
  obtain ⟨j0⟩ := hne
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hy j0)
  set S := ∑ j, w j * Real.exp (y j) with hS
  set V := ∑ j, w j * y j ^ 2 with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (sq_nonneg _))
  rcases eq_or_lt_of_le hM0 with hM | hM
  · subst hM
    have hy0 : ∀ j, y j = 0 := fun j => abs_nonpos_iff.mp (hy j)
    have : S = 1 := by simp [hS, hy0, hw1]
    rw [this]
    simp
  · set t := min 1 M⁻¹ with ht
    have ht0 : 0 < t := lt_min one_pos (inv_pos.mpr hM)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htM : t * M ≤ 1 := by
      calc t * M ≤ M⁻¹ * M := mul_le_mul_of_nonneg_right (min_le_right _ _) hM.le
        _ = 1 := inv_mul_cancel₀ hM.ne'
    have hty : ∀ j, |t * y j| ≤ 1 := by
      intro j
      rw [abs_mul, abs_of_pos ht0]
      calc t * |y j| ≤ t * M := mul_le_mul_of_nonneg_left (hy j) ht0.le
        _ ≤ 1 := htM
    have hVM : V ≤ M ^ 2 := by
      calc V ≤ ∑ j, w j * M ^ 2 := by
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_mul_of_nonneg_left _ (hw j)
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hy j) 2
        _ = M ^ 2 := by rw [← Finset.sum_mul, hw1, one_mul]
    set T := ∑ j, w j * Real.exp (t * y j) with hT
    have hT1 : 1 + t ^ 2 * V / 3 ≤ T := by
      calc 1 + t ^ 2 * V / 3 = ∑ j, w j * (1 + t * y j + (t * y j) ^ 2 / 3) := by
            simp only [mul_add, Finset.sum_add_distrib, mul_one, hw1]
            have e1 : ∑ j, w j * (t * y j) = t * ∑ j, w j * y j := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
            have e2 : ∑ j, w j * ((t * y j) ^ 2 / 3) = t ^ 2 * V / 3 := by
              rw [hV, Finset.mul_sum, Finset.sum_div]
              exact Finset.sum_congr rfl (fun j _ => by ring)
            rw [e1, e2, hmean]; ring
        _ ≤ T := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (exp_ge_quad (hty j)) (hw j))
    have hu : t ^ 2 * V ≤ 1 := by
      calc t ^ 2 * V ≤ t ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hVM (sq_nonneg _)
        _ = (t * M) ^ 2 := by ring
        _ ≤ 1 := by
          have : 0 ≤ t * M := mul_nonneg ht0.le hM.le
          nlinarith
    have hTpos : 0 < T := by
      have : 0 ≤ t ^ 2 * V := mul_nonneg (sq_nonneg _) hV0
      linarith
    have hlogT : t ^ 2 * V / 4 ≤ Real.log T := by
      set u := t ^ 2 * V / 3 with hu'
      have hu0 : 0 ≤ u := by positivity
      have hlog1 : 1 - (1 + u)⁻¹ ≤ Real.log (1 + u) := Real.one_sub_inv_le_log_of_pos (by linarith)
      have hmono : Real.log (1 + u) ≤ Real.log T := Real.log_le_log (by linarith) hT1
      have : t ^ 2 * V / 4 ≤ 1 - (1 + u)⁻¹ := by
        rw [show 1 - (1 + u)⁻¹ = u / (1 + u) by field_simp; ring]
        rw [le_div_iff₀ (by linarith)]
        nlinarith
      linarith
    have hJ : T ^ (1 / t) ≤ S := by
      have h := Real.rpow_arith_mean_le_arith_mean_rpow (s := Finset.univ) w (fun j => Real.exp (t * y j))
        (fun j _ => hw j) hw1 (fun j _ => (Real.exp_pos _).le) (p := 1 / t)
        (by rw [le_div_iff₀ ht0]; linarith)
      refine h.trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Real.exp_mul]
      congr 2
      field_simp
    have hlogJ : (1 / t) * Real.log T ≤ Real.log S := by
      rw [← Real.log_rpow hTpos]
      exact Real.log_le_log (Real.rpow_pos_of_pos hTpos _) hJ
    have key : t * V / 4 ≤ (1 / t) * Real.log T := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ht0]
      nlinarith
    linarith

end Formalism.NuclearRankWeightBounds.P
