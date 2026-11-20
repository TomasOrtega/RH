import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronChi
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RectShiftChi
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.IntegralEqIntervalIntegralAddCompl

open Complex MeasureTheory

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

/- English proof (translation)
Establish `hpi : (2 * Real.pi : ℂ) ≠ 0`. Establish `: (2 * Real.pi : ℝ) ≠ 0` using `by positivity`. Conclude with `this` after adjusting the coercions. Rewrite using `[hS, mul_sub, ← mul_assoc, mul_one_div_cancel hpi, one_mul]`. Take the linear combination `(-I) * hrect + (V0 - V1 - 2 * Real.pi * R) * Complex.I_sq`.
-/
theorem tail_shift_alg (S R V0 V1 E a b : ℂ) (hS : S = (1 / (2 * Real.pi) : ℂ) * (V0 + E))
    (hrect : a - b + I * V0 - I * V1 = 2 * Real.pi * I * R) :
    (2 * Real.pi : ℂ) * (S - R) = E + I * (a - b) + V1 := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  rw [hS, mul_sub, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  linear_combination (-I) * hrect + (V0 - V1 - 2 * Real.pi * R) * Complex.I_sq

/- English proof (translation)
Take `⟨hint, hS⟩` from `Formalism.ZeroFreeDirichlet.perron_formula_character N χ y hy 2 (by norm_num)`. Establish `hrect` using `Formalism.ZeroFreeDirichlet.rectangle_contour_shift_character N χ hχ y (by linarith) σ₁ 2 T ∅ hσ₁ hσ₁' (by norm_num) hT (by simp) (fun w h1 h2 h3 hL => absurd hL (hzf w h1 h2 h3)) (by simp)`. Simplify using `only [Finset.sum_empty, sub_zero] at hrect`. Unfold `Formalism.ZF.rectInt at hrect`. Rewrite `hS` using `[← integral_add_compl (s := Set.Ioc (-T) T) measurableSet_Ioc hint, ← intervalIntegral.integral_of_le (a := -T) (b := T) (by linarith)]`.

Conclude with `tail_shift_alg _ _ _ _ _ _ _ hS hrect`.
-/
theorem tail_shift_identity {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (y σ₁ T : ℝ)
    (hy : 1 ≤ y) (hσ₁ : 0 < σ₁) (hσ₁' : σ₁ < 1) (hT : 0 < T)
    (hzf : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ 2 → |w.im| ≤ T → DirichletCharacter.LFunction χ w ≠ 0) :
    (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ y - Formalism.ZeroFreeDirichlet.negLD χ 1 * y) =
      (∫ t in (Set.Ioc (-T) T)ᶜ, Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I))
      + I * ((∫ x in σ₁..2, Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
          - ∫ x in σ₁..2, Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (T : ℂ) * I))
      + ∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ y ((σ₁ : ℂ) + (u : ℂ) * I) := by
  obtain ⟨hint, hS⟩ := Formalism.ZeroFreeDirichlet.perron_formula_character N χ y hy 2 (by norm_num)
  have hrect := Formalism.ZeroFreeDirichlet.rectangle_contour_shift_character N χ hχ y (by linarith) σ₁ 2 T ∅ hσ₁ hσ₁' (by norm_num) hT
    (by simp) (fun w h1 h2 h3 hL => absurd hL (hzf w h1 h2 h3)) (by simp)
  simp only [Finset.sum_empty, sub_zero] at hrect
  unfold Formalism.ZF.rectInt at hrect
  rw [← integral_add_compl (s := Set.Ioc (-T) T) measurableSet_Ioc hint,
    ← intervalIntegral.integral_of_le (a := -T) (b := T) (by linarith)] at hS
  exact tail_shift_alg _ _ _ _ _ _ _ hS hrect

end Formalism.HermitianLattices.Ext.BoxTail
