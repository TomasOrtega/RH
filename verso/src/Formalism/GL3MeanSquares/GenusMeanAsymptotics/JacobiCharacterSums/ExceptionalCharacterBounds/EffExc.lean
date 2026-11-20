import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.LfunctionOneLowerBound
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LDerivNearOne

open Formalism.ZeroFreeDirichlet

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP

/- English proof (translation)
Establish `hy0 : 0 < y` using `by linarith`. Establish `hs : 0 < Real.sqrt y` using `Real.sqrt_pos.mpr hy0`. Establish `hge : 1 ≤ Real.sqrt y` using `Real.one_le_sqrt.mpr hy`. Establish `h1 : Real.log y = 2 * Real.log (Real.sqrt y)` using `by conv_lhs => rw [← Real.mul_self_sqrt hy0.le]`. Rewrite using `[Real.log_mul hs.ne' hs.ne']`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1` using `Real.log_le_sub_one_of_pos hs`. Establish `h0 : 0 ≤ Real.log (Real.sqrt y)` using `Real.log_nonneg hge`. Establish `hsq : Real.sqrt y * Real.sqrt y = y` using `Real.mul_self_sqrt hy0.le`. Rewrite using `[h1]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem log_sq_le_four_mul_of_one_le {y : ℝ} (hy : 1 ≤ y) : Real.log y ^ 2 ≤ 4 * y := by
  have hy0 : 0 < y := by linarith
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hge : 1 ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy
  have h1 : Real.log y = 2 * Real.log (Real.sqrt y) := by
    conv_lhs => rw [← Real.mul_self_sqrt hy0.le]
    rw [Real.log_mul hs.ne' hs.ne']; ring
  have h2 : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 := Real.log_le_sub_one_of_pos hs
  have h0 : 0 ≤ Real.log (Real.sqrt y) := Real.log_nonneg hge
  have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  rw [h1]; nlinarith

/- English proof (translation)
Take `⟨CD, hCD⟩` from `lfunction_deriv_near_one`. Use `set C := max CD 1 with hCdef`. Establish `hC1 : 1 ≤ C` using `le_max_right _ _`. Use `⟨min (1 / 12) (1 / (480 * C)), lt_min (by norm_num) (by positivity), ?_⟩` and prove the remaining obligations. Introduce `q _ χ β hχ2 hχ hz`.

Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)`. Establish `hq0 : (0 : ℝ) < q` using `by linarith`. Establish `hq2 : (q : ℝ) ^ (-((2 : ℕ) : ℝ)) = ((q : ℝ) ^ 2)⁻¹`. Rewrite using `[Real.rpow_neg hq0.le, Real.rpow_natCast]`. Rewrite using `[hq2]`.

Establish `hβ1 : β < 1`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using h) hz`. Use `set ℓ := Real.log (3 * (q : ℝ)) with hℓdef`.

Establish `hℓ1 : 1 ≤ ℓ`. Establish `h3 : Real.exp 1 ≤ 3 * (q : ℝ)`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Establish `hℓsq : ℓ ^ 2 ≤ 12 * q`. Use `log_sq_le_four_mul_of_one_le (y := 3 * (q : ℝ)) (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hℓle : ℓ ≤ 12 * q` using `by nlinarith`. Establish `hmin1 : min (1 / 12) (1 / (480 * C)) ≤ 1 / 12` using `min_le_left _ _`.

Establish `hmin2 : min (1 / 12) (1 / (480 * C)) ≤ 1 / (480 * C)` using `min_le_right _ _`. Establish `hmin0 : 0 < min (1 / 12) (1 / (480 * C))` using `lt_min (by norm_num) (by positivity)`. Establish `hqq : (0 : ℝ) < (q : ℝ) ^ 2` using `by positivity`. Distinguish the cases in `hcase : β < 1 - 1 / ℓ`. Establish `hinv : 1 / (12 * (q : ℝ) ^ 2) ≤ 1 / ℓ`.

Apply `one_div_le_one_div_of_le (by linarith)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `: min (1 / 12) (1 / (480 * C)) * ((q : ℝ) ^ 2)⁻¹ ≤ 1 / (12 * (q : ℝ) ^ 2)`. Rewrite using `[show 1 / (12 * (q : ℝ) ^ 2) = 1 / 12 * ((q : ℝ) ^ 2)⁻¹ by field_simp]`. Conclude with `mul_le_mul_of_nonneg_right hmin1 (by positivity)`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `push Not at hcase`. Establish `hf : ∀ t ∈ Set.Icc β 1, HasDerivWithinAt (fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) (deriv (DirichletCharacter.LFunction χ) (t : ℂ)) (Set.Icc β 1) t` using `fun t _ => ((DirichletCharacter.differentiable_LFunction hχ (t : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt`. Establish `hbound : ∀ t ∈ Set.Ico β 1, ‖deriv (DirichletCharacter.LFunction χ) (t : ℂ)‖ ≤ C * ℓ ^ 2`. Introduce `t ht`.

Establish `h` using `hCD q χ hχ t (by rw [← hℓdef]; linarith [ht.1]) ht.2.le`. Establish `: CD * Real.log (3 * q) ^ 2 ≤ C * Real.log (3 * q) ^ 2` using `mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)`. Conclude with `h.trans (by rw [← hℓdef] at this; exact this)`. Establish `hmv` using `norm_image_sub_le_of_norm_deriv_le_segment' hf hbound 1 ⟨hβ1.le, le_refl 1⟩`. Simplify using `only [Complex.ofReal_one, hz, sub_zero] at hmv`.

Establish `hL1` using `lfunction_one_lower_bound q χ hχ2 hχ`. Establish `hre : (DirichletCharacter.LFunction χ 1).re ≤ ‖DirichletCharacter.LFunction χ 1‖` using `Complex.re_le_norm _`. Establish `hδ : 0 ≤ 1 - β` using `by linarith`. Establish `hkey : 1 / (20 * ((q : ℝ) + 1)) ≤ C * (12 * q) * (1 - β)`. Establish `: C * ℓ ^ 2 * (1 - β) ≤ C * (12 * q) * (1 - β)`.

Apply `mul_le_mul_of_nonneg_right _ hδ` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_left hℓsq (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkey2 : 1 ≤ 480 * C * (q : ℝ) ^ 2 * (1 - β)`. Rewrite `hkey` using `[div_le_iff₀ (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `: min (1 / 12) (1 / (480 * C)) * ((q : ℝ) ^ 2)⁻¹ ≤ 1 - β`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_le_iff₀ (by positivity)]; linarith`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem excBoundEff : ExcBoundAt 2 := by
  obtain ⟨CD, hCD⟩ := lfunction_deriv_near_one
  set C := max CD 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  refine ⟨min (1 / 12) (1 / (480 * C)), lt_min (by norm_num) (by positivity), ?_⟩
  intro q _ χ β hχ2 hχ hz
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hq2 : (q : ℝ) ^ (-((2 : ℕ) : ℝ)) = ((q : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hq0.le, Real.rpow_natCast]
  rw [hq2]
  have hβ1 : β < 1 := by
    by_contra h
    push Not at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using h) hz
  set ℓ := Real.log (3 * (q : ℝ)) with hℓdef
  have hℓ1 : 1 ≤ ℓ := by
    have h3 : Real.exp 1 ≤ 3 * (q : ℝ) := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ ℓ := Real.log_le_log (Real.exp_pos 1) h3
  have hℓsq : ℓ ^ 2 ≤ 12 * q := by
    have := log_sq_le_four_mul_of_one_le (y := 3 * (q : ℝ)) (by linarith)
    linarith
  have hℓle : ℓ ≤ 12 * q := by nlinarith
  have hmin1 : min (1 / 12) (1 / (480 * C)) ≤ 1 / 12 := min_le_left _ _
  have hmin2 : min (1 / 12) (1 / (480 * C)) ≤ 1 / (480 * C) := min_le_right _ _
  have hmin0 : 0 < min (1 / 12) (1 / (480 * C)) := lt_min (by norm_num) (by positivity)
  have hqq : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  by_cases hcase : β < 1 - 1 / ℓ
  ·
    have hinv : 1 / (12 * (q : ℝ) ^ 2) ≤ 1 / ℓ := by
      apply one_div_le_one_div_of_le (by linarith)
      nlinarith
    have : min (1 / 12) (1 / (480 * C)) * ((q : ℝ) ^ 2)⁻¹ ≤ 1 / (12 * (q : ℝ) ^ 2) := by
      rw [show 1 / (12 * (q : ℝ) ^ 2) = 1 / 12 * ((q : ℝ) ^ 2)⁻¹ by field_simp]
      exact mul_le_mul_of_nonneg_right hmin1 (by positivity)
    linarith
  · push Not at hcase
    have hf : ∀ t ∈ Set.Icc β 1, HasDerivWithinAt (fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ))
        (deriv (DirichletCharacter.LFunction χ) (t : ℂ)) (Set.Icc β 1) t := fun t _ =>
      ((DirichletCharacter.differentiable_LFunction hχ (t : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
    have hbound : ∀ t ∈ Set.Ico β 1, ‖deriv (DirichletCharacter.LFunction χ) (t : ℂ)‖ ≤ C * ℓ ^ 2 := by
      intro t ht
      have h := hCD q χ hχ t (by rw [← hℓdef]; linarith [ht.1]) ht.2.le
      have : CD * Real.log (3 * q) ^ 2 ≤ C * Real.log (3 * q) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      exact h.trans (by rw [← hℓdef] at this; exact this)
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hf hbound 1 ⟨hβ1.le, le_refl 1⟩
    simp only [Complex.ofReal_one, hz, sub_zero] at hmv
    have hL1 := lfunction_one_lower_bound q χ hχ2 hχ
    have hre : (DirichletCharacter.LFunction χ 1).re ≤ ‖DirichletCharacter.LFunction χ 1‖ :=
      Complex.re_le_norm _
    have hδ : 0 ≤ 1 - β := by linarith
    have hkey : 1 / (20 * ((q : ℝ) + 1)) ≤ C * (12 * q) * (1 - β) := by
      have : C * ℓ ^ 2 * (1 - β) ≤ C * (12 * q) * (1 - β) := by
        apply mul_le_mul_of_nonneg_right _ hδ
        exact mul_le_mul_of_nonneg_left hℓsq (by linarith)
      linarith
    have hkey2 : 1 ≤ 480 * C * (q : ℝ) ^ 2 * (1 - β) := by
      rw [div_le_iff₀ (by positivity)] at hkey
      nlinarith
    have : min (1 / 12) (1 / (480 * C)) * ((q : ℝ) ^ 2)⁻¹ ≤ 1 - β := by
      calc min (1 / 12) (1 / (480 * C)) * ((q : ℝ) ^ 2)⁻¹ ≤ 1 / (480 * C) * ((q : ℝ) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hmin2 (by positivity)
        _ = 1 / (480 * C * (q : ℝ) ^ 2) := by field_simp
        _ ≤ 1 - β := by
            rw [div_le_iff₀ (by positivity)]; linarith
    linarith

end Formalism.HermitianLattices.Ext.SupplyAP
