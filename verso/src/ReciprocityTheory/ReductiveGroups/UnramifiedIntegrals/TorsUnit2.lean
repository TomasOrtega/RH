import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementK
import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsNoPrimeToPTorsion
import Formalism.EllipticTorsion.EllipticTorsionProofs.TorInt

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F WeierstrassCurve

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Establish `n4 : ‖(4 : K)‖ = 1`. Rewrite using `[show (4 : K) = 2 * 2 by norm_num, norm_mul, h2]; norm_num`. Establish `h40 : (4 : K) ≠ 0`. Introduce `h0`. Rewrite `n4` using `[h0, norm_zero]`.

Conclude with `zero_ne_one n4`. Establish `h20 : (2 : K) ≠ 0`. Introduce `h0`. Rewrite `h2` using `[h0, norm_zero]`. Conclude with `zero_ne_one h2`.

Establish `hW : Formalism.ELL.IntegralModel (Formalism.L2.Th1.A.shortW g2 g3)`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Formalism.L2.Th1.A.shortW, n4, hg2, hg3.le]`. Establish `hD : ‖(Formalism.L2.Th1.A.shortW g2 g3).Δ‖ = 1`. Establish `: (Formalism.L2.Th1.A.shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2`. Simplify using `only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, Formalism.L2.Th1.A.shortW]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hΔ]`. Establish `n27 : ‖(27 : K)‖ = 1`. Rewrite using `[show (27 : K) = 3 * 3 * 3 by norm_num, norm_mul, norm_mul, h3]; norm_num`.

Establish `hg2' : ‖g2‖ = 1`. Establish `hs : ‖27 * g3 ^ 2‖ < 1`. Rewrite using `[norm_mul, n27, one_mul, norm_pow]`. Conclude with `pow_lt_one₀ (norm_nonneg _) hg3 (by norm_num)`. Establish `h1 : ‖g2 ^ 3‖ = 1`.

Establish `e : g2 ^ 3 = (g2 ^ 3 - 27 * g3 ^ 2) + 27 * g3 ^ 2` using `by ring`. Rewrite using `[e, Formalism.ELL.FormalGroupPointsTorsion.dom (by rw [hΔ]; exact hs), hΔ]`. Rewrite `h1` using `[norm_pow]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1`. Take `⟨hx, -⟩` from `Formalism.ELL.torsionIntegral_of Formalism.ELL.formal_group_points_no_prime_to_p_torsion K _ hW hD n hn x y h hP`.

Assume the negation of the conclusion as `hne`. Establish `hx1 : ‖x‖ < 1` using `lt_of_le_of_ne hx hne`. Establish `heq : y ^ 2 = x ^ 3 - g2 / 4 * x - g3 / 4`. Use `(Affine.equation_iff x y).1 h.1` as an intermediate fact. Simplify using `only [Formalism.L2.Th1.A.shortW] at this`.

Take the linear combination `this`. Establish `hy1 : ‖y‖ < 1`. Establish `: ‖y ^ 2‖ < 1`. Rewrite using `[heq]`. Use `Formalism.ELL.FormalGroupPointsTorsion.sub_lt (Formalism.ELL.FormalGroupPointsTorsion.sub_lt ?_ ?_) ?_` and prove the remaining obligations.

Rewrite using `[norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx1 (by norm_num)`. Rewrite using `[norm_mul, norm_div, n4, hg2']`. Simplify using `using hx1`. Rewrite using `[norm_div, n4]`. Simplify using `using hg3`.

Rewrite `this` using `[norm_pow]`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `absurd this (not_lt.2 (one_le_pow₀ hc))`. Establish `hQ : Formalism.ELL.InFormalGroupPoints (Affine.Point.some x y h + Affine.Point.some x y h)`.

Distinguish the cases in `hy : y = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY x y`. Rewrite using `[Affine.Point.add_self_of_Y_eq hy, Affine.Point.zero_def]`. Discharge the goal by the elementary cases of `trivial`. Rewrite using `[Affine.Point.add_self_of_Y_ne hy] show 1 < ‖_‖`. Establish `hy0 : y ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hy (by simp [Affine.negY, Formalism.L2.Th1.A.shortW])`. Rewrite using `[Affine.slope_of_Y_ne rfl hy]`. Simplify using `only [Affine.addX, Affine.negY, Formalism.L2.Th1.A.shortW]`. Establish `e : ((3 * x ^ 2 + 2 * 0 * x + -g2 / 4 - 0 * y) / (y - (-y - 0 * x - 0))) ^ 2 + 0 * ((3 * x ^ 2 + 2 * 0 * x + -g2 / 4 - 0 * y) / (y - (-y - 0 * x - 0))) - 0 - x - x = ((-(g2 / 4) + 3 * x ^ 2) / (2 * y)) ^ 2 + (-x - x)`.

Establish `: y - (-y - 0 * x - 0) = 2 * y` using `by ring`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `hnum : ‖-(g2 / 4) + 3 * x ^ 2‖ = 1`.

Establish `ha : ‖-(g2 / 4)‖ = 1` using `by rw [norm_neg, norm_div, n4, hg2']; norm_num`. Rewrite using `[Formalism.ELL.FormalGroupPointsTorsion.dom, ha]`. Rewrite using `[ha, norm_mul, h3, one_mul, norm_pow]`. Conclude with `pow_lt_one₀ (norm_nonneg _) hx1 (by norm_num)`. Establish `hyp : 0 < ‖y‖` using `norm_pos_iff.2 hy0`.

Establish `hl : 1 < ‖((-(g2 / 4) + 3 * x ^ 2) / (2 * y)) ^ 2‖`. Rewrite using `[norm_pow, norm_div, hnum, norm_mul, h2, one_mul]`. Conclude with `one_lt_pow₀ ((one_lt_div hyp).2 hy1) (by norm_num)`. Establish `hs : ‖-x - x‖ < 1` using `Formalism.ELL.FormalGroupPointsTorsion.sub_lt (by rwa [norm_neg]) hx1`. Rewrite using `[Formalism.ELL.FormalGroupPointsTorsion.dom (hs.trans hl)]`.

Conclude with `hl`. Establish `hQ0 : Affine.Point.some x y h + Affine.Point.some x y h = 0`. Use `Formalism.ELL.formal_group_points_no_prime_to_p_torsion K _ hW hD n hn _ hQ ?_` and prove the remaining obligations. Rewrite using `[nsmul_add, hP, add_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := by`.

Use `Nat.odd_iff.2 (by omega : n % 2 = 1)` as an intermediate fact. Conclude with `this`. Use `Affine.Point.some_ne_zero h ?_` and prove the remaining obligations. Rewrite `hP` using `[add_nsmul, one_nsmul, mul_comm, mul_nsmul', two_nsmul, hQ0, nsmul_zero, zero_add]`. Conclude with `hP`.
-/
theorem torsUnit2 (K : Type) [NormedField K] [IsUltrametricDist K] (g2 g3 : K) (h2 : ‖(2 : K)‖ = 1)
    (h3 : ‖(3 : K)‖ = 1) (hg2 : ‖g2‖ ≤ 1) (hg3 : ‖g3‖ < 1) (hΔ : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1)
    (n : ℕ) (hn : ‖(n : K)‖ = 1) (hen : ¬ 2 ∣ n) (x y : K)
    (h : (Formalism.L2.Th1.A.shortW g2 g3).toAffine.Nonsingular x y) (hP : n • (Affine.Point.some x y h) = 0) : ‖x‖ = 1 := by
  have n4 : ‖(4 : K)‖ = 1 := by
    rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h2]; norm_num
  have h40 : (4 : K) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at n4; exact zero_ne_one n4
  have h20 : (2 : K) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h2; exact zero_ne_one h2
  have hW : Formalism.ELL.IntegralModel (Formalism.L2.Th1.A.shortW g2 g3) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Formalism.L2.Th1.A.shortW, n4, hg2, hg3.le]
  have hD : ‖(Formalism.L2.Th1.A.shortW g2 g3).Δ‖ = 1 := by
    have : (Formalism.L2.Th1.A.shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2 := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈, Formalism.L2.Th1.A.shortW]
      field_simp
      ring
    rw [this, hΔ]

  have n27 : ‖(27 : K)‖ = 1 := by
    rw [show (27 : K) = 3 * 3 * 3 by norm_num, norm_mul, norm_mul, h3]; norm_num
  have hg2' : ‖g2‖ = 1 := by
    have hs : ‖27 * g3 ^ 2‖ < 1 := by
      rw [norm_mul, n27, one_mul, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hg3 (by norm_num)
    have h1 : ‖g2 ^ 3‖ = 1 := by
      have e : g2 ^ 3 = (g2 ^ 3 - 27 * g3 ^ 2) + 27 * g3 ^ 2 := by ring
      rw [e, Formalism.ELL.FormalGroupPointsTorsion.dom (by rw [hΔ]; exact hs), hΔ]
    rw [norm_pow] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  obtain ⟨hx, -⟩ := Formalism.ELL.torsionIntegral_of Formalism.ELL.formal_group_points_no_prime_to_p_torsion K _ hW hD n hn x y h hP
  by_contra hne
  have hx1 : ‖x‖ < 1 := lt_of_le_of_ne hx hne
  have heq : y ^ 2 = x ^ 3 - g2 / 4 * x - g3 / 4 := by
    have := (Affine.equation_iff x y).1 h.1
    simp only [Formalism.L2.Th1.A.shortW] at this
    linear_combination this
  have hy1 : ‖y‖ < 1 := by
    have : ‖y ^ 2‖ < 1 := by
      rw [heq]
      refine Formalism.ELL.FormalGroupPointsTorsion.sub_lt (Formalism.ELL.FormalGroupPointsTorsion.sub_lt ?_ ?_) ?_
      · rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx1 (by norm_num)
      · rw [norm_mul, norm_div, n4, hg2']; simpa using hx1
      · rw [norm_div, n4]; simpa using hg3
    rw [norm_pow] at this
    by_contra hc
    push Not at hc
    exact absurd this (not_lt.2 (one_le_pow₀ hc))

  have hQ : Formalism.ELL.InFormalGroupPoints (Affine.Point.some x y h + Affine.Point.some x y h) := by
    by_cases hy : y = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY x y
    · rw [Affine.Point.add_self_of_Y_eq hy, Affine.Point.zero_def]; trivial
    · rw [Affine.Point.add_self_of_Y_ne hy]
      show 1 < ‖_‖
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact hy (by simp [Affine.negY, Formalism.L2.Th1.A.shortW])
      rw [Affine.slope_of_Y_ne rfl hy]
      simp only [Affine.addX, Affine.negY, Formalism.L2.Th1.A.shortW]
      have e : ((3 * x ^ 2 + 2 * 0 * x + -g2 / 4 - 0 * y) / (y - (-y - 0 * x - 0))) ^ 2 +
          0 * ((3 * x ^ 2 + 2 * 0 * x + -g2 / 4 - 0 * y) / (y - (-y - 0 * x - 0))) - 0 - x - x
          = ((-(g2 / 4) + 3 * x ^ 2) / (2 * y)) ^ 2 + (-x - x) := by
        have : y - (-y - 0 * x - 0) = 2 * y := by ring
        rw [this]; ring
      rw [e]
      have hnum : ‖-(g2 / 4) + 3 * x ^ 2‖ = 1 := by
        have ha : ‖-(g2 / 4)‖ = 1 := by rw [norm_neg, norm_div, n4, hg2']; norm_num
        rw [Formalism.ELL.FormalGroupPointsTorsion.dom, ha]
        rw [ha, norm_mul, h3, one_mul, norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hx1 (by norm_num)
      have hyp : 0 < ‖y‖ := norm_pos_iff.2 hy0
      have hl : 1 < ‖((-(g2 / 4) + 3 * x ^ 2) / (2 * y)) ^ 2‖ := by
        rw [norm_pow, norm_div, hnum, norm_mul, h2, one_mul]
        exact one_lt_pow₀ ((one_lt_div hyp).2 hy1) (by norm_num)
      have hs : ‖-x - x‖ < 1 :=
        Formalism.ELL.FormalGroupPointsTorsion.sub_lt (by rwa [norm_neg]) hx1
      rw [Formalism.ELL.FormalGroupPointsTorsion.dom (hs.trans hl)]
      exact hl
  have hQ0 : Affine.Point.some x y h + Affine.Point.some x y h = 0 := by
    refine Formalism.ELL.formal_group_points_no_prime_to_p_torsion K _ hW hD n hn _ hQ ?_
    rw [nsmul_add, hP, add_zero]
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := by
    have := Nat.odd_iff.2 (by omega : n % 2 = 1)
    exact this
  refine Affine.Point.some_ne_zero h ?_
  rw [add_nsmul, one_nsmul, mul_comm, mul_nsmul', two_nsmul, hQ0, nsmul_zero, zero_add] at hP
  exact hP

end ReciprocityTheory.ChartRestriction.L1
