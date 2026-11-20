import Mathlib
import Formalism.PeriodIntegrals.PhSchurConv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurConvolution.MapMulApply

/- English proof (translation)
Use `open MeasureTheory in`. Use `open scoped InnerProductSpace in`. Introduce `G _ _ _ _ _ _ μ _ _ _ Hσ _ _ σ d w hU hF hw`. Establish `hd : (d : ℂ) ≠ 0` using `by exact_mod_cast (ne_of_gt hF.1)`. Establish `hstard : star (d : ℂ) = d` using `Complex.conj_ofReal d`.

Establish `hinv : (d : ℂ) * (d : ℂ)⁻¹ = 1` using `mul_inv_cancel₀ hd`. Establish `h1 : σ 1 = 1` using `hU.1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `PI.PhSchurConv.PhConv`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [PI.PhSchurConv.coefM]`. Rewrite using `[h1, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hw]`. Simplify using the standard rewrite rules. Introduce `g`. Simplify using `only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]`.

Rewrite using `[(PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_inv hU)]`. Simplify using `only [star_mul', star_star, hstard]`. Apply the tactic sequence `try ring`. Introduce `x y`. Establish `key : ∀ g, PI.PhSchurConv.phOf σ w d g * PI.PhSchurConv.phOf σ w d (x⁻¹ * g⁻¹ * y) = ((d : ℂ) * d) * (⟪σ y w, σ g (σ x w)⟫_ℂ * star ⟪w, σ g w⟫_ℂ)`.

Introduce `g`. Simplify using `only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]`. Rewrite using `[(PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_conv hU), PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner (σ g (σ x w)) (σ y w)]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨hi, he⟩` from `hF.2 (σ x w) (σ y w) w w`.

Repeatedly rewrite using `[key]`. Use `⟨hi.const_mul _, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_const_mul, he]`. Simplify using `only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]`. Rewrite using `[PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner w (σ y w), div_eq_mul_inv]`.

Take the linear combination `(⟪w, σ x w⟫_ℂ * ⟪σ y w, w⟫_ℂ * d) * hinv`. Introduce `u u'`. Establish `key : ∀ g, PI.PhSchurConv.phOf σ w d g * ⟪u', σ g u⟫_ℂ = (d : ℂ) * (⟪u', σ g u⟫_ℂ * star ⟪w, σ g w⟫_ℂ)`. Introduce `g`. Simplify using `only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨hi, he⟩` from `hF.2 u u' w w`. Repeatedly rewrite using `[key]`. Use `⟨hi.const_mul _, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_const_mul, he, div_eq_mul_inv]`.

Take the linear combination `(⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ) * hinv`.
-/
theorem schur_orthogonality_idempotent : PI.PhSchurConv.SchurConv := by
  open MeasureTheory in
  open scoped InnerProductSpace in
  intro G _ _ _ _ _ _ μ _ _ _ Hσ _ _ σ d w hU hF hw
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hF.1)
  have hstard : star (d : ℂ) = d := Complex.conj_ofReal d
  have hinv : (d : ℂ) * (d : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hd
  have h1 : σ 1 = 1 := hU.1
  refine ⟨?_, ?_⟩
  · unfold PI.PhSchurConv.PhConv
    refine ⟨?_, ?_, ?_⟩
    · simp only [PI.PhSchurConv.coefM]
      rw [h1, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hw]
      simp
    · intro g
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      rw [(PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_inv hU)]
      simp only [star_mul', star_star, hstard]
      try ring
    · intro x y
      have key : ∀ g, PI.PhSchurConv.phOf σ w d g * PI.PhSchurConv.phOf σ w d (x⁻¹ * g⁻¹ * y)
          = ((d : ℂ) * d) * (⟪σ y w, σ g (σ x w)⟫_ℂ * star ⟪w, σ g w⟫_ℂ) := by
        intro g
        simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
        rw [(PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_conv hU), PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner (σ g (σ x w)) (σ y w)]
        ring
      obtain ⟨hi, he⟩ := hF.2 (σ x w) (σ y w) w w
      simp_rw [key]
      refine ⟨hi.const_mul _, ?_⟩
      rw [integral_const_mul, he]
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      rw [PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner w (σ y w), div_eq_mul_inv]
      linear_combination (⟪w, σ x w⟫_ℂ * ⟪σ y w, w⟫_ℂ * d) * hinv
  · intro u u'
    have key : ∀ g, PI.PhSchurConv.phOf σ w d g * ⟪u', σ g u⟫_ℂ
        = (d : ℂ) * (⟪u', σ g u⟫_ℂ * star ⟪w, σ g w⟫_ℂ) := by
      intro g
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      ring
    obtain ⟨hi, he⟩ := hF.2 u u' w w
    simp_rw [key]
    refine ⟨hi.const_mul _, ?_⟩
    rw [integral_const_mul, he, div_eq_mul_inv]
    linear_combination (⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ) * hinv
