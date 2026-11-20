import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

/- English proof (translation)
Introduce `n h μ _ F c M hF hy`. Take `⟨hpos, hfin⟩` from `h1 n h`. Establish `: IsFiniteMeasure (volume.restrict (ballH h))` using `isFiniteMeasure_restrict.2 hfin.ne`. Establish `hsm : StronglyMeasurable (Function.uncurry F)` using `hF.stronglyMeasurable`. Establish `hint : Integrable (Function.uncurry F) ((volume.restrict (ballH h)).prod μ)`.

Rewrite using `[integrable_prod_iff' hsm.aestronglyMeasurable]`. Use `⟨hy.mono fun y hy => hy.1, ?_⟩` and prove the remaining obligations. Use `Integrable.of_bound ?_ M ?_` and prove the remaining obligations. Conclude with `(hsm.norm.integral_prod_left' (μ := volume.restrict (ballH h))).aestronglyMeasurable`. Use `filter_upwards [hy] with y hy`.

Establish `e : ∀ x, ‖Function.uncurry F (x, y)‖ = |F x y|` using `fun x => Real.norm_eq_abs _`. Simplify using `only [e]`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]`. Conclude with `hy.2.1`. Use `⟨hint.integral_prod_left, ?_⟩` and prove the remaining obligations.

Establish `hvol : (volume (ballH h)).toReal ≠ 0` using `(ENNReal.toReal_pos hpos.ne' hfin.ne).ne'`. Establish `hreal : volume.real (ballH h) = (volume (ballH h)).toReal` using `rfl`. Establish `hin : ∀ᵐ y ∂μ, ∫ v in ballH h, F v y = c * (volume (ballH h)).toReal` using `by filter_upwards [hy] with y hy`. Establish `e` using `hy.2.2`. Rewrite `e` using `[setAverage_eq, hreal, smul_eq_mul]`.

Clear denominators, using `at e ⊢` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hswap` using `integral_integral_swap hint`. Rewrite using `[setAverage_eq, hreal, smul_eq_mul, hswap, integral_congr_ae hin, integral_const, smul_eq_mul]`. Simplify using `only [measureReal_def]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem ConeFubini.proof (h1 : BallVolume.Statement) : ConeFubini.Statement := by
  intro n h μ _ F c M hF hy
  obtain ⟨hpos, hfin⟩ := h1 n h
  have : IsFiniteMeasure (volume.restrict (ballH h)) := isFiniteMeasure_restrict.2 hfin.ne
  have hsm : StronglyMeasurable (Function.uncurry F) := hF.stronglyMeasurable

  have hint : Integrable (Function.uncurry F) ((volume.restrict (ballH h)).prod μ) := by
    rw [integrable_prod_iff' hsm.aestronglyMeasurable]
    refine ⟨hy.mono fun y hy => hy.1, ?_⟩
    refine Integrable.of_bound ?_ M ?_
    · exact (hsm.norm.integral_prod_left' (μ := volume.restrict (ballH h))).aestronglyMeasurable
    · filter_upwards [hy] with y hy
      have e : ∀ x, ‖Function.uncurry F (x, y)‖ = |F x y| := fun x => Real.norm_eq_abs _
      simp only [e]
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
      exact hy.2.1
  refine ⟨hint.integral_prod_left, ?_⟩
  have hvol : (volume (ballH h)).toReal ≠ 0 := (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  have hreal : volume.real (ballH h) = (volume (ballH h)).toReal := rfl

  have hin : ∀ᵐ y ∂μ, ∫ v in ballH h, F v y = c * (volume (ballH h)).toReal := by
    filter_upwards [hy] with y hy
    have e := hy.2.2
    rw [setAverage_eq, hreal, smul_eq_mul] at e
    field_simp at e ⊢
    linarith
  have hswap := integral_integral_swap hint
  rw [setAverage_eq, hreal, smul_eq_mul, hswap, integral_congr_ae hin, integral_const, smul_eq_mul]
  simp only [measureReal_def]
  field_simp
