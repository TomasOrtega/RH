import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SumVonMangoldtNotCoprimeLe
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.AbsZeroTermSecondDifferenceLe
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LeOfSecondDifferenceBound

open Complex Finset ArithmeticFunction

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma chebyshev_smoothing_identity_complex (ψ Z SY Sy MY My A : ℂ) (y h : ℝ) :
    ((y * h : ℝ) : ℂ) * (ψ + Z)
      = -(((y : ℂ) * SY - ((y * (1 + h) : ℝ) : ℂ) * Sy) - ((y * (1 + h) - y : ℝ) : ℂ) * ψ)
        + (((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z)
        + ((y : ℂ) * (SY - A * ((y * (1 + h) : ℝ) : ℂ) + MY)
            - ((y * (1 + h) : ℝ) : ℂ) * (Sy - A * (y : ℂ) + My)) := by
  push_cast; ring

/- English proof (translation)
Rewrite using `[hSY, hSy]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma chebyshev_smoothing_identity_real (ψ SY Sy GY Gy y h : ℝ) (hSY : SY = (y * (1 + h)) * Real.log (y * (1 + h))
      - (1 + Real.eulerMascheroniConstant) * (y * (1 + h)) + GY)
    (hSy : Sy = y * Real.log y - (1 + Real.eulerMascheroniConstant) * y + Gy) :
    (y * h) * (ψ - y)
      = -((y * SY - (y * (1 + h)) * Sy) - (y * (1 + h) - y) * ψ)
        + (y * ((y * (1 + h)) * Real.log (y * (1 + h))
            - (1 + Real.eulerMascheroniConstant) * (y * (1 + h)))
          - (y * (1 + h)) * (y * Real.log y - (1 + Real.eulerMascheroniConstant) * y) - y * h * y)
        + (y * GY - (y * (1 + h)) * Gy) := by
  rw [hSY, hSy]; ring

/- English proof (translation)
Use `⟨Real.exp_pos _, Real.exp_le_one_iff.2 ?_⟩` and prove the remaining obligations. Use `mul_nonneg hc0.le (Real.sqrt_nonneg (Real.log y))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma exp_neg_sqrt_log_mem_unit_interval {c₀ y : ℝ} (hc0 : 0 < c₀) :
    0 < Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) ∧
      Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) ≤ 1 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.2 ?_⟩
  have := mul_nonneg hc0.le (Real.sqrt_nonneg (Real.log y))
  linarith

/- English proof (translation)
Take `⟨hh0, hh1⟩` from `exp_neg_sqrt_log_mem_unit_interval (y := y) hc0`. Use `set h := Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) with hh`. Establish `hypos : 0 < y` using `by linarith`. Establish `hyY : y ≤ y * (1 + h)` using `by nlinarith`. Establish `hY0 : 0 ≤ y * (1 + h)` using `by positivity`.

Establish `hβ : ∀ β ∈ B, 1 / 2 ≤ β ∧ β < 1`. Introduce `β hβB`. Take `⟨_, hreg, hzero, _⟩` from `hB.2.1 β hβB`. Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)`. Simplify using `only [InRegion, Complex.ofReal_im, abs_zero, zero_add, Complex.ofReal_re] at hreg`.

Establish `hl : Real.log 2 ≤ Real.log ((q : ℝ) * 2)` using `Real.log_le_log (by norm_num) (by linarith)`. Establish `hl2` using `Real.log_two_gt_d9`. Establish `hlpos : 0 < Real.log ((q : ℝ) * 2)` using `by linarith`. Establish `hfrac : c₁ / Real.log ((q : ℝ) * 2) ≤ 1 / 2`. Rewrite using `[div_le_iff₀ hlpos]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨by linarith, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hge`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using not_lt.1 hge) hzero`. Use `set f : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) with hf`.

Establish `hfb : ∀ n, ‖f n‖ ≤ Λ n`. Introduce `n`. Simplify using `only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]`. Conclude with `mul_le_of_le_one_right vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _)`. Establish `hS : ∀ x, Schi χ x = weightedPartialSumUpTo f x` using `fun x => rfl`.

Establish `hP : psiChi χ y = partialSumUpTo f y` using `rfl`. Establish `hD` using `norm_weightedSum_sub_le f hfb (show (1:ℝ) ≤ y by linarith) hyY`. Use `set MY := ∑ β ∈ B, (((y * (1 + h) : ℝ) : ℂ)) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)) with hMY`. Use `set My := ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)) with hMy`. Use `set Z := ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / (β : ℂ) with hZ`.

Establish `hid` using `chebyshev_smoothing_identity_complex (psiChi χ y) Z (Schi χ (y * (1 + h))) (Schi χ y) MY My (negLD χ 1) y h`. Establish `hM : ‖((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z‖ ≤ 2 * y ^ 2 * h ^ 2`. Establish `e : ((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z = ∑ β ∈ B, (((y * (1 + h) * (y ^ β / (β * (β - 1))) - y * ((y * (1 + h)) ^ β / (β * (β - 1))) + y * h * (y ^ β / β) : ℝ)) : ℂ)`. Rewrite using `[hMY, hMy, hZ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `β _`. Rewrite using `[← Complex.ofReal_cpow hypos.le, ← Complex.ofReal_cpow hY0]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `β hβB`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs]`. Conclude with `abs_zero_term_second_difference_le (by linarith) hh0 hh1 (hβ β hβB).1 (hβ β hβB).2`.

Use `_ = (B.card : ℝ) * (2 * y ^ 2 * h ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ 1 * (2 * y ^ 2 * h ^ 2) := by`. Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Conclude with `hB.1` after adjusting the coercions. Use `_ = 2 * y ^ 2 * h ^ 2 := one_mul _`.

Establish `hEY` using `hE (y * (1 + h)) hyY`. Establish `hEy` using `hE y le_rfl`. Use `set eY := Real.exp (-cs * Real.sqrt (Real.log (y * (1 + h))))`. Use `set ey := Real.exp (-cs * Real.sqrt (Real.log y))`. Establish `hmain : y * h * ‖psiChi χ y + Z‖ ≤ (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h))) + 2 * y ^ 2 * h ^ 2 + y * (Cs * (y * (1 + h)) * eY) + y * (1 + h) * (Cs * y * ey)`.

Establish `hn : ‖((y * h : ℝ) : ℂ) * (psiChi χ y + Z)‖ = y * h * ‖psiChi χ y + Z‖`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]`. Rewrite using `[← hn, hid]`. Establish `hD' : ‖((y : ℂ) * Schi χ (y * (1 + h)) - ((y * (1 + h) : ℝ) : ℂ) * Schi χ y) - ((y * (1 + h) - y : ℝ) : ℂ) * psiChi χ y‖ ≤ (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h)))`. Rewrite using `[hS, hS, hP]`.

Conclude with `hD`. Establish `h1 : ‖(y : ℂ) * (Schi χ (y * (1 + h)) - negLD χ 1 * ((y * (1 + h) : ℝ) : ℂ) + MY)‖ ≤ y * (Cs * (y * (1 + h)) * eY)`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos]`. Conclude with `mul_le_mul_of_nonneg_left hEY hypos.le`. Establish `h2 : ‖((y * (1 + h) : ℝ) : ℂ) * (Schi χ y - negLD χ 1 * (y : ℂ) + My)‖ ≤ y * (1 + h) * (Cs * y * ey)`.

Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hY0]`. Conclude with `mul_le_mul_of_nonneg_left hEy hY0`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(norm_add_le _ _).trans (by rw [norm_neg])`. Conclude with `norm_sub_le _ _`.

Use `_ ≤ _ := by linarith`. Establish `hey` using `exp_neg_sqrt_log_le_sq (cs := cs) hc0.le hcs (show (1:ℝ) ≤ y by linarith) (le_refl y)`. Establish `heY` using `exp_neg_sqrt_log_le_sq (cs := cs) hc0.le hcs (show (1:ℝ) ≤ y by linarith) hyY`. Conclude with `le_of_second_difference_bound hy hc0 hc01 hCs hh (Real.exp_pos _).le (Real.exp_pos _).le hey heY hmain`.
-/
lemma chebyshev_character_nonprincipal_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c₁ : ℝ}
    (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 20) (B : Finset ℝ) (hB : ExcZeros c₁ χ B)
    {cs Cs c₀ y : ℝ} (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1) (hcs : c₀ ≤ cs) (hCs : 0 ≤ Cs) (hy : 2 ≤ y)
    (hE : ∀ z : ℝ, y ≤ z →
      ‖Schi χ z - negLD χ 1 * z + ∑ β ∈ B, (z : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤
        Cs * z * Real.exp (-cs * Real.sqrt (Real.log z))) :
    ‖psiChi χ y + ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
      (128 / c₀ ^ 2 + 2 + 4 * Cs) * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by
  obtain ⟨hh0, hh1⟩ := exp_neg_sqrt_log_mem_unit_interval (y := y) hc0
  set h := Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) with hh
  have hypos : 0 < y := by linarith
  have hyY : y ≤ y * (1 + h) := by nlinarith
  have hY0 : 0 ≤ y * (1 + h) := by positivity

  have hβ : ∀ β ∈ B, 1 / 2 ≤ β ∧ β < 1 := by
    intro β hβB
    obtain ⟨_, hreg, hzero, _⟩ := hB.2.1 β hβB
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
    simp only [InRegion, Complex.ofReal_im, abs_zero, zero_add, Complex.ofReal_re] at hreg
    have hl : Real.log 2 ≤ Real.log ((q : ℝ) * 2) := Real.log_le_log (by norm_num) (by linarith)
    have hl2 := Real.log_two_gt_d9
    have hlpos : 0 < Real.log ((q : ℝ) * 2) := by linarith
    have hfrac : c₁ / Real.log ((q : ℝ) * 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ hlpos]; linarith
    refine ⟨by linarith, ?_⟩
    by_contra hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by simpa using not_lt.1 hge) hzero
  set f : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) with hf
  have hfb : ∀ n, ‖f n‖ ≤ Λ n := by
    intro n
    simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _)
  have hS : ∀ x, Schi χ x = weightedPartialSumUpTo f x := fun x => rfl
  have hP : psiChi χ y = partialSumUpTo f y := rfl
  have hD := norm_weightedSum_sub_le f hfb (show (1:ℝ) ≤ y by linarith) hyY
  set MY := ∑ β ∈ B, (((y * (1 + h) : ℝ) : ℂ)) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)) with hMY
  set My := ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)) with hMy
  set Z := ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / (β : ℂ) with hZ
  have hid := chebyshev_smoothing_identity_complex (psiChi χ y) Z (Schi χ (y * (1 + h))) (Schi χ y) MY My (negLD χ 1) y h

  have hM : ‖((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z‖ ≤
      2 * y ^ 2 * h ^ 2 := by
    have e : ((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z
        = ∑ β ∈ B, (((y * (1 + h) * (y ^ β / (β * (β - 1))) - y * ((y * (1 + h)) ^ β / (β * (β - 1)))
            + y * h * (y ^ β / β) : ℝ)) : ℂ) := by
      rw [hMY, hMy, hZ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro β _
      rw [← Complex.ofReal_cpow hypos.le, ← Complex.ofReal_cpow hY0]
      push_cast; ring
    rw [e]
    calc _ ≤ ∑ β ∈ B, ‖(((y * (1 + h) * (y ^ β / (β * (β - 1)))
              - y * ((y * (1 + h)) ^ β / (β * (β - 1))) + y * h * (y ^ β / β) : ℝ)) : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ β ∈ B, 2 * y ^ 2 * h ^ 2 := by
          apply Finset.sum_le_sum
          intro β hβB
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact abs_zero_term_second_difference_le (by linarith) hh0 hh1 (hβ β hβB).1 (hβ β hβB).2
      _ = (B.card : ℝ) * (2 * y ^ 2 * h ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (2 * y ^ 2 * h ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hB.1
      _ = 2 * y ^ 2 * h ^ 2 := one_mul _
  have hEY := hE (y * (1 + h)) hyY
  have hEy := hE y le_rfl
  set eY := Real.exp (-cs * Real.sqrt (Real.log (y * (1 + h))))
  set ey := Real.exp (-cs * Real.sqrt (Real.log y))
  have hmain : y * h * ‖psiChi χ y + Z‖ ≤
      (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h)))
        + 2 * y ^ 2 * h ^ 2 + y * (Cs * (y * (1 + h)) * eY) + y * (1 + h) * (Cs * y * ey) := by
    have hn : ‖((y * h : ℝ) : ℂ) * (psiChi χ y + Z)‖ = y * h * ‖psiChi χ y + Z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [← hn, hid]
    have hD' : ‖((y : ℂ) * Schi χ (y * (1 + h)) - ((y * (1 + h) : ℝ) : ℂ) * Schi χ y)
        - ((y * (1 + h) - y : ℝ) : ℂ) * psiChi χ y‖
        ≤ (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h))) := by
      rw [hS, hS, hP]; exact hD
    have h1 : ‖(y : ℂ) * (Schi χ (y * (1 + h)) - negLD χ 1 * ((y * (1 + h) : ℝ) : ℂ) + MY)‖
        ≤ y * (Cs * (y * (1 + h)) * eY) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos]
      exact mul_le_mul_of_nonneg_left hEY hypos.le
    have h2 : ‖((y * (1 + h) : ℝ) : ℂ) * (Schi χ y - negLD χ 1 * (y : ℂ) + My)‖
        ≤ y * (1 + h) * (Cs * y * ey) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hY0]
      exact mul_le_mul_of_nonneg_left hEy hY0
    calc _ ≤ ‖-(((y : ℂ) * Schi χ (y * (1 + h)) - ((y * (1 + h) : ℝ) : ℂ) * Schi χ y)
              - ((y * (1 + h) - y : ℝ) : ℂ) * psiChi χ y)
            + (((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z)‖
          + ‖(y : ℂ) * (Schi χ (y * (1 + h)) - negLD χ 1 * ((y * (1 + h) : ℝ) : ℂ) + MY)
            - ((y * (1 + h) : ℝ) : ℂ) * (Schi χ y - negLD χ 1 * (y : ℂ) + My)‖ := norm_add_le _ _
      _ ≤ (‖((y : ℂ) * Schi χ (y * (1 + h)) - ((y * (1 + h) : ℝ) : ℂ) * Schi χ y)
              - ((y * (1 + h) - y : ℝ) : ℂ) * psiChi χ y‖
            + ‖((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z‖)
          + (‖(y : ℂ) * (Schi χ (y * (1 + h)) - negLD χ 1 * ((y * (1 + h) : ℝ) : ℂ) + MY)‖
            + ‖((y * (1 + h) : ℝ) : ℂ) * (Schi χ y - negLD χ 1 * (y : ℂ) + My)‖) := by
          gcongr
          · exact (norm_add_le _ _).trans (by rw [norm_neg])
          · exact norm_sub_le _ _
      _ ≤ _ := by linarith
  have hey := exp_neg_sqrt_log_le_sq (cs := cs) hc0.le hcs (show (1:ℝ) ≤ y by linarith) (le_refl y)
  have heY := exp_neg_sqrt_log_le_sq (cs := cs) hc0.le hcs (show (1:ℝ) ≤ y by linarith) hyY
  exact le_of_second_difference_bound hy hc0 hc01 hCs hh (Real.exp_pos _).le (Real.exp_pos _).le hey heY hmain

/- English proof (translation)
Take `⟨hh0, hh1⟩` from `exp_neg_sqrt_log_mem_unit_interval (y := y) hc0`. Use `set h := Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) with hh`. Establish `hypos : 0 < y` using `by linarith`. Establish `hyY : y ≤ y * (1 + h)` using `by nlinarith`. Establish `hY0 : 0 ≤ y * (1 + h)` using `by positivity`.

Use `set f : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) with hf`. Establish `hfb : ∀ n, ‖f n‖ ≤ Λ n`. Introduce `n`. Simplify using `only [hf, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg, le_refl]`. Establish `hS : ∀ x, weightedPartialSumUpTo f x = ((Formalism.Sz x : ℝ) : ℂ)`.

Introduce `x`. Simplify using `only [weightedPartialSumUpTo, Formalism.Sz, hf]`. Use `push_cast`. Both sides reduce to the same expression. Use `set ψ₀ := ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n with hψ₀`.

Establish `hP : partialSumUpTo f y = ((ψ₀ : ℝ) : ℂ)`. Simplify using `only [partialSumUpTo, hf, hψ₀]`. Use `push_cast`. Both sides reduce to the same expression. Use `set nc := ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n * (if n.Coprime q then 0 else 1) with hnc`.

Establish `hpsi : psiChi (1 : DirichletCharacter ℂ q) y = ((ψ₀ - nc : ℝ) : ℂ)`. Simplify using `only [psiChi, one_apply_natCast, hψ₀, hnc]`. Use `push_cast`. Rewrite using `[← Finset.sum_sub_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `n _`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hD` using `norm_weightedSum_sub_le f hfb (show (1:ℝ) ≤ y by linarith) hyY`. Rewrite `hD` using `[hS, hS, hP]`. Establish `hD' : |(y * Formalism.Sz (y * (1 + h)) - (y * (1 + h)) * Formalism.Sz y) - (y * (1 + h) - y) * ψ₀| ≤ (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h)))`.

Establish `e : ((y : ℂ) * ((Formalism.Sz (y * (1 + h)) : ℝ) : ℂ) - ((y * (1 + h) : ℝ) : ℂ) * ((Formalism.Sz y : ℝ) : ℂ)) - ((y * (1 + h) - y : ℝ) : ℂ) * ((ψ₀ : ℝ) : ℂ) = (((y * Formalism.Sz (y * (1 + h)) - (y * (1 + h)) * Formalism.Sz y) - (y * (1 + h) - y) * ψ₀ : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite `hD` using `[e, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `hD`. Establish `hGY` using `hG (y * (1 + h)) hyY`. Establish `hGy` using `hG y le_rfl`.

Use `set eY := Real.exp (-cg * Real.sqrt (Real.log (y * (1 + h))))`. Use `set ey := Real.exp (-cg * Real.sqrt (Real.log y))`. Establish `hid` using `chebyshev_smoothing_identity_real ψ₀ (Formalism.Sz (y * (1 + h))) (Formalism.Sz y) (Formalism.Gz (y * (1 + h))) (Formalism.Gz y) y h (by simp only [Formalism.Gz]; ring) (by simp only [Formalism.Gz]; ring)`. Establish `hW` using `abs_main_term_second_difference_le (γ := Real.eulerMascheroniConstant) hypos hh0`. Establish `hmain : y * h * |ψ₀ - y| ≤ (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h))) + 2 * y ^ 2 * h ^ 2 + y * (Kg * (y * (1 + h)) * eY) + y * (1 + h) * (Kg * y * ey)`.

Rewrite using `[← abs_of_pos (show 0 < y * h by positivity), ← abs_mul, hid]`. Establish `h1 : |y * Formalism.Gz (y * (1 + h)) - (y * (1 + h)) * Formalism.Gz y| ≤ y * (Kg * (y * (1 + h)) * eY) + y * (1 + h) * (Kg * y * ey)`. Use `(abs_sub _ _).trans ?_` and prove the remaining obligations. Rewrite using `[abs_mul, abs_mul, abs_of_pos hypos, abs_of_nonneg hY0]`. Conclude with `add_le_add (mul_le_mul_of_nonneg_left hGY hypos.le) (mul_le_mul_of_nonneg_left hGy hY0)`.

Establish `hsq : 0 ≤ y ^ 2 * h ^ 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `hey` using `exp_neg_sqrt_log_le_sq (cs := cg) hc0.le hcg (show (1:ℝ) ≤ y by linarith) (le_refl y)`. Establish `heY` using `exp_neg_sqrt_log_le_sq (cs := cg) hc0.le hcg (show (1:ℝ) ≤ y by linarith) hyY`. Establish `hfin` using `le_of_second_difference_bound hy hc0 hc01 hKg hh (Real.exp_pos _).le (Real.exp_pos _).le hey heY hmain`.

Establish `hq0 : q ≠ 0` using `NeZero.ne q`. Establish `hnc1` using `sum_vonMangoldt_not_coprime_le q hq0 ⌊y⌋₊`. Rewrite `hnc1` using `[← hnc]`. Establish `hK : (Nat.log 2 ⌊y⌋₊ : ℝ) * Real.log 2 ≤ Real.log y`. Establish `hfl : ⌊y⌋₊ ≠ 0`.

Establish `: 1 ≤ ⌊y⌋₊` using `Nat.le_floor (by norm_num; linarith)`. Use linear arithmetic over natural numbers and integers. Establish `h2 : ((2 ^ Nat.log 2 ⌊y⌋₊ : ℕ) : ℝ) ≤ y`. Use `Nat.pow_log_le_self 2 hfl` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Real.log_pow]`. Apply `Real.log_le_log (by positivity)` to reduce the goal to its premises. Conclude with `h2` after adjusting the coercions. Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 hq0`. Establish `hlq0 : 0 ≤ Real.log q` using `Real.log_nonneg hq1`.

Establish `hlq : Real.log q ≤ c₀ / 4 * Real.sqrt (Real.log y)`. Use `Real.log_le_log (by linarith) hq` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Then use the resulting hypothesis. Establish `hncb` using `mul_le_of_log_bounds hy hc0 hc01 hK (by positivity) hlq0 hlq`. Apply the tactic sequence `have hnc0 : 0 ≤ nc := Finset.sum_nonneg fun n _ => mul_nonneg vonMangoldt_nonneg (by split_ifs <;> norm_num)`.

Rewrite using `[hpsi]`. Establish `e : ((ψ₀ - nc : ℝ) : ℂ) - (y : ℂ) = (((ψ₀ - y) - nc : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[e, Complex.norm_real, Real.norm_eq_abs]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma chebyshev_principal_character_bound {q : ℕ} [NeZero q] {cg Kg c₀ y : ℝ} (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1)
    (hcg : c₀ ≤ cg) (hKg : 0 ≤ Kg) (hy : 2 ≤ y)
    (hq : (q : ℝ) ≤ Real.exp (c₀ / 4 * Real.sqrt (Real.log y)))
    (hG : ∀ z : ℝ, y ≤ z → |Formalism.Gz z| ≤ Kg * z * Real.exp (-cg * Real.sqrt (Real.log z))) :
    ‖psiChi (1 : DirichletCharacter ℂ q) y - y‖ ≤
      (128 / c₀ ^ 2 + 2 + 4 * Kg) * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y))
        + 16 * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by
  obtain ⟨hh0, hh1⟩ := exp_neg_sqrt_log_mem_unit_interval (y := y) hc0
  set h := Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) with hh
  have hypos : 0 < y := by linarith
  have hyY : y ≤ y * (1 + h) := by nlinarith
  have hY0 : 0 ≤ y * (1 + h) := by positivity
  set f : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) with hf
  have hfb : ∀ n, ‖f n‖ ≤ Λ n := by
    intro n
    simp only [hf, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg, le_refl]
  have hS : ∀ x, weightedPartialSumUpTo f x = ((Formalism.Sz x : ℝ) : ℂ) := by
    intro x; simp only [weightedPartialSumUpTo, Formalism.Sz, hf]; push_cast; rfl
  set ψ₀ := ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n with hψ₀
  have hP : partialSumUpTo f y = ((ψ₀ : ℝ) : ℂ) := by
    simp only [partialSumUpTo, hf, hψ₀]; push_cast; rfl
  set nc := ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n * (if n.Coprime q then 0 else 1) with hnc
  have hpsi : psiChi (1 : DirichletCharacter ℂ q) y = ((ψ₀ - nc : ℝ) : ℂ) := by
    simp only [psiChi, one_apply_natCast, hψ₀, hnc]
    push_cast
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> simp

  have hD := norm_weightedSum_sub_le f hfb (show (1:ℝ) ≤ y by linarith) hyY
  rw [hS, hS, hP] at hD
  have hD' : |(y * Formalism.Sz (y * (1 + h)) - (y * (1 + h)) * Formalism.Sz y) - (y * (1 + h) - y) * ψ₀|
      ≤ (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h))) := by
    have e : ((y : ℂ) * ((Formalism.Sz (y * (1 + h)) : ℝ) : ℂ) - ((y * (1 + h) : ℝ) : ℂ) * ((Formalism.Sz y : ℝ) : ℂ))
        - ((y * (1 + h) - y : ℝ) : ℂ) * ((ψ₀ : ℝ) : ℂ)
        = (((y * Formalism.Sz (y * (1 + h)) - (y * (1 + h)) * Formalism.Sz y) - (y * (1 + h) - y) * ψ₀ : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs] at hD
    exact hD
  have hGY := hG (y * (1 + h)) hyY
  have hGy := hG y le_rfl
  set eY := Real.exp (-cg * Real.sqrt (Real.log (y * (1 + h))))
  set ey := Real.exp (-cg * Real.sqrt (Real.log y))
  have hid := chebyshev_smoothing_identity_real ψ₀ (Formalism.Sz (y * (1 + h))) (Formalism.Sz y) (Formalism.Gz (y * (1 + h))) (Formalism.Gz y) y h
    (by simp only [Formalism.Gz]; ring) (by simp only [Formalism.Gz]; ring)
  have hW := abs_main_term_second_difference_le (γ := Real.eulerMascheroniConstant) hypos hh0
  have hmain : y * h * |ψ₀ - y| ≤
      (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h)))
        + 2 * y ^ 2 * h ^ 2 + y * (Kg * (y * (1 + h)) * eY) + y * (1 + h) * (Kg * y * ey) := by
    rw [← abs_of_pos (show 0 < y * h by positivity), ← abs_mul, hid]
    have h1 : |y * Formalism.Gz (y * (1 + h)) - (y * (1 + h)) * Formalism.Gz y|
        ≤ y * (Kg * (y * (1 + h)) * eY) + y * (1 + h) * (Kg * y * ey) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hypos, abs_of_nonneg hY0]
      exact add_le_add (mul_le_mul_of_nonneg_left hGY hypos.le) (mul_le_mul_of_nonneg_left hGy hY0)
    have hsq : 0 ≤ y ^ 2 * h ^ 2 := by positivity
    calc _ ≤ |-((y * Formalism.Sz (y * (1 + h)) - (y * (1 + h)) * Formalism.Sz y) - (y * (1 + h) - y) * ψ₀)|
          + |y * ((y * (1 + h)) * Real.log (y * (1 + h))
            - (1 + Real.eulerMascheroniConstant) * (y * (1 + h)))
          - (y * (1 + h)) * (y * Real.log y - (1 + Real.eulerMascheroniConstant) * y) - y * h * y|
          + |y * Formalism.Gz (y * (1 + h)) - (y * (1 + h)) * Formalism.Gz y| := abs_add_three _ _ _
      _ ≤ _ := by rw [abs_neg]; linarith
  have hey := exp_neg_sqrt_log_le_sq (cs := cg) hc0.le hcg (show (1:ℝ) ≤ y by linarith) (le_refl y)
  have heY := exp_neg_sqrt_log_le_sq (cs := cg) hc0.le hcg (show (1:ℝ) ≤ y by linarith) hyY
  have hfin := le_of_second_difference_bound hy hc0 hc01 hKg hh (Real.exp_pos _).le (Real.exp_pos _).le hey heY hmain

  have hq0 : q ≠ 0 := NeZero.ne q
  have hnc1 := sum_vonMangoldt_not_coprime_le q hq0 ⌊y⌋₊
  rw [← hnc] at hnc1
  have hK : (Nat.log 2 ⌊y⌋₊ : ℝ) * Real.log 2 ≤ Real.log y := by
    have hfl : ⌊y⌋₊ ≠ 0 := by
      have : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith)
      omega
    have h2 : ((2 ^ Nat.log 2 ⌊y⌋₊ : ℕ) : ℝ) ≤ y := by
      have := Nat.pow_log_le_self 2 hfl
      calc ((2 ^ Nat.log 2 ⌊y⌋₊ : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast this
        _ ≤ y := Nat.floor_le hypos.le
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast h2
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hq0
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlq : Real.log q ≤ c₀ / 4 * Real.sqrt (Real.log y) := by
    have := Real.log_le_log (by linarith) hq
    rwa [Real.log_exp] at this
  have hncb := mul_le_of_log_bounds hy hc0 hc01 hK (by positivity) hlq0 hlq
  have hnc0 : 0 ≤ nc := Finset.sum_nonneg fun n _ =>
    mul_nonneg vonMangoldt_nonneg (by split_ifs <;> norm_num)
  rw [hpsi]
  have e : ((ψ₀ - nc : ℝ) : ℂ) - (y : ℂ) = (((ψ₀ - y) - nc : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  calc |(ψ₀ - y) - nc| ≤ |ψ₀ - y| + |nc| := abs_sub _ _
    _ ≤ _ := by rw [abs_of_nonneg hnc0]; linarith

/- English proof (translation)
Introduce `hS hG c₁ hc₁ hc₁'`. Take `⟨cs, Cs, hcs, hSm⟩` from `hS c₁ hc₁ hc₁'`. Take `⟨cg, Kg, hcg, hGz⟩` from `hG`. Use `set c₀ := min (min cs cg) 1 with hc0def`. Establish `hc0 : 0 < c₀` using `lt_min (lt_min hcs hcg) one_pos`.

Establish `hc01 : c₀ ≤ 1` using `min_le_right _ _`. Establish `hc0s : c₀ ≤ cs` using `(min_le_left _ _).trans (min_le_left _ _)`. Establish `hc0g : c₀ ≤ cg` using `(min_le_left _ _).trans (min_le_right _ _)`. Use `set Cs' := max Cs 0`. Use `set Kg' := max Kg 0`.

Use `⟨c₀ / 4, 128 / c₀ ^ 2 + 2 + 4 * Cs' + 4 * Kg' + 16, by positivity, ?_⟩` and prove the remaining obligations. Introduce `q _ χ B x hB hx hq`. Establish `he4 : 0 ≤ x * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log x))` using `by positivity`. Establish `hCs' : 0 ≤ Cs'` using `le_max_right _ _`. Establish `hKg' : 0 ≤ Kg'` using `le_max_right _ _`.

Distinguish the cases in `hχ : χ = 1`. Establish `hB0 : B = ∅` using `Finset.eq_empty_of_forall_notMem fun β hβ => (hB.2.1 β hβ).1 hχ`. Substitute `hχ hB0` using the available equality. Rewrite using `[if_pos rfl, Finset.sum_empty, add_zero]`. Establish `hG' : ∀ z : ℝ, x ≤ z → |Formalism.Gz z| ≤ Kg' * z * Real.exp (-cg * Real.sqrt (Real.log z))`.

Introduce `z hz`. Use `(hGz z (by linarith)).trans ?_` and prove the remaining obligations. Establish `: 0 ≤ z * Real.exp (-cg * Real.sqrt (Real.log z))`. Establish `: 0 ≤ z` using `by linarith`. Check the signs of the components of the expression.

Use polynomial arithmetic with `[le_max_left Kg 0]`. Use `chebyshev_principal_character_bound (q := q) hc0 hc01 hc0g hKg' hx hq hG'` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[if_neg hχ, sub_zero]`. Establish `hE : ∀ z : ℝ, x ≤ z → ‖Schi χ z - negLD χ 1 * z + ∑ β ∈ B, (z : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤ Cs' * z * Real.exp (-cs * Real.sqrt (Real.log z))`.

Introduce `z hz`. Establish `hqz : (q : ℝ) ≤ Real.exp (cs * Real.sqrt (Real.log z))`. Use `hq.trans (Real.exp_le_exp.2 ?_)` and prove the remaining obligations. Establish `h1 : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log z)` using `Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hz)`. Establish `h0 : 0 ≤ Real.sqrt (Real.log x)` using `Real.sqrt_nonneg _`.

Establish `h0' : 0 ≤ Real.sqrt (Real.log z)` using `Real.sqrt_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Use `(hSm q χ B z hχ hB (by linarith) hqz).trans ?_` and prove the remaining obligations. Establish `: 0 ≤ z * Real.exp (-cs * Real.sqrt (Real.log z))`. Establish `: 0 ≤ z` using `by linarith`.

Check the signs of the components of the expression. Use polynomial arithmetic with `[le_max_left Cs 0]`. Use `chebyshev_character_nonprincipal_bound χ hχ hc₁ hc₁' B hB hc0 hc01 hc0s hCs' hx hE` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem chebyshev_character_bound_of : PsiChiBoundOf := by
  intro hS hG c₁ hc₁ hc₁'
  obtain ⟨cs, Cs, hcs, hSm⟩ := hS c₁ hc₁ hc₁'
  obtain ⟨cg, Kg, hcg, hGz⟩ := hG
  set c₀ := min (min cs cg) 1 with hc0def
  have hc0 : 0 < c₀ := lt_min (lt_min hcs hcg) one_pos
  have hc01 : c₀ ≤ 1 := min_le_right _ _
  have hc0s : c₀ ≤ cs := (min_le_left _ _).trans (min_le_left _ _)
  have hc0g : c₀ ≤ cg := (min_le_left _ _).trans (min_le_right _ _)
  set Cs' := max Cs 0
  set Kg' := max Kg 0
  refine ⟨c₀ / 4, 128 / c₀ ^ 2 + 2 + 4 * Cs' + 4 * Kg' + 16, by positivity, ?_⟩
  intro q _ χ B x hB hx hq
  have he4 : 0 ≤ x * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log x)) := by positivity
  have hCs' : 0 ≤ Cs' := le_max_right _ _
  have hKg' : 0 ≤ Kg' := le_max_right _ _
  by_cases hχ : χ = 1
  · have hB0 : B = ∅ := Finset.eq_empty_of_forall_notMem fun β hβ => (hB.2.1 β hβ).1 hχ
    subst hχ hB0
    rw [if_pos rfl, Finset.sum_empty, add_zero]
    have hG' : ∀ z : ℝ, x ≤ z → |Formalism.Gz z| ≤ Kg' * z * Real.exp (-cg * Real.sqrt (Real.log z)) := by
      intro z hz
      refine (hGz z (by linarith)).trans ?_
      have : 0 ≤ z * Real.exp (-cg * Real.sqrt (Real.log z)) := by
        have : 0 ≤ z := by linarith
        positivity
      nlinarith [le_max_left Kg 0]
    have := chebyshev_principal_character_bound (q := q) hc0 hc01 hc0g hKg' hx hq hG'
    nlinarith
  · rw [if_neg hχ, sub_zero]
    have hE : ∀ z : ℝ, x ≤ z →
        ‖Schi χ z - negLD χ 1 * z + ∑ β ∈ B, (z : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤
          Cs' * z * Real.exp (-cs * Real.sqrt (Real.log z)) := by
      intro z hz
      have hqz : (q : ℝ) ≤ Real.exp (cs * Real.sqrt (Real.log z)) := by
        refine hq.trans (Real.exp_le_exp.2 ?_)
        have h1 : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log z) :=
          Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hz)
        have h0 : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
        have h0' : 0 ≤ Real.sqrt (Real.log z) := Real.sqrt_nonneg _
        nlinarith
      refine (hSm q χ B z hχ hB (by linarith) hqz).trans ?_
      have : 0 ≤ z * Real.exp (-cs * Real.sqrt (Real.log z)) := by
        have : 0 ≤ z := by linarith
        positivity
      nlinarith [le_max_left Cs 0]
    have := chebyshev_character_nonprincipal_bound χ hχ hc₁ hc₁' B hB hc0 hc01 hc0s hCs' hx hE
    nlinarith

end Formalism.ZeroFreeDirichlet
