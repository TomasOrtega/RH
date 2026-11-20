import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Qf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorExplicitFormula

noncomputable section

open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2

namespace GlobalTheory.CompanionTheory.DInt2.WMaj

/- English proof (translation)
Simplify using `[al]`.
-/
theorem al_re (h : M22) : (al h).re = h 0 0 := by simp [al]
/- English proof (translation)
Simplify using `[al]`.
-/
theorem al_im (h : M22) : (al h).im = h 1 0 := by simp [al]
/- English proof (translation)
Simplify using `[be]`.
-/
theorem be_re (h : M22) : (be h).re = h 0 1 := by simp [be]
/- English proof (translation)
Simplify using `[be]`.
-/
theorem be_im (h : M22) : (be h).im = h 1 1 := by simp [be]

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hΔ`.
-/
theorem al_ne (h : M22) (hΔ : 0 < (Matrix.of h).det) : al h ≠ 0 :=
  GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hΔ

/- English proof (translation)
Establish `hn : Complex.normSq (al h) ≠ 0`. Simplify `al_ne h hΔ` using `[Complex.normSq_eq_zero]`. Rewrite using `[Complex.div_im, uu, Complex.sq_norm, Matrix.det_fin_two, al_re, al_im, be_re, be_im]`. Simplify using `only [Matrix.of_apply]`. Clear the denominators using the available nonvanishing facts.
-/
theorem im_ratio (h : M22) (hΔ : 0 < (Matrix.of h).det) : (be h / al h).im = uu h := by
  have hn : Complex.normSq (al h) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using al_ne h hΔ
  rw [Complex.div_im, uu, Complex.sq_norm, Matrix.det_fin_two, al_re, al_im, be_re, be_im]
  simp only [Matrix.of_apply]
  field_simp

/- English proof (translation)
Establish `: 0 < ‖al h‖` using `norm_pos_iff.mpr (al_ne h hΔ)`. Unfold `uu`. Check the signs of the components of the expression.
-/
theorem uu_pos (h : M22) (hΔ : 0 < (Matrix.of h).det) : 0 < uu h := by
  have : 0 < ‖al h‖ := norm_pos_iff.mpr (al_ne h hΔ)
  unfold uu
  positivity

/- English proof (translation)
Establish `e` using `GlobalTheory.CompanionTheory.WeightClosed.main k hk h hΔ`. Express the relevant statement in the definitionally equal form `w0 k h = (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) * (al h) ^ (-(2 * (k : ℤ) - 1)) * Complex.exp (2 * Real.pi * Complex.I * (be h / al h)) at e`. Establish `hre : (2 * (Real.pi : ℂ) * Complex.I * (be h / al h)).re = -(2 * Real.pi * uu h)`. Rewrite using `[← im_ratio h hΔ]`. Simplify using `[Complex.mul_re, Complex.mul_im]`.

Rewrite using `[e, norm_mul, norm_mul, norm_pow, norm_zpow, Complex.norm_exp, hre, Complex.norm_real, Real.norm_of_nonneg hΔ.le]`.
-/
theorem norm_weight_closed_form (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    ‖w0 k h‖ = (Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) *
      Real.exp (-(2 * Real.pi * uu h)) := by
  have e := GlobalTheory.CompanionTheory.WeightClosed.main k hk h hΔ
  change w0 k h = (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) * (al h) ^ (-(2 * (k : ℤ) - 1)) *
    Complex.exp (2 * Real.pi * Complex.I * (be h / al h)) at e
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (be h / al h)).re = -(2 * Real.pi * uu h) := by
    rw [← im_ratio h hΔ]
    simp [Complex.mul_re, Complex.mul_im]
  rw [e, norm_mul, norm_mul, norm_pow, norm_zpow, Complex.norm_exp, hre, Complex.norm_real,
    Real.norm_of_nonneg hΔ.le]

/- English proof (translation)
Take `⟨i00, i01, i10, i11⟩` from `GlobalTheory.CompanionTheory.WeightClosed.inv_entries h`. Establish `hα` using `al_ne h hΔ`. Establish `hD : (((Matrix.of h).det : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hΔ.ne'`. Establish `hdi : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹`. Rewrite using `[Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`.

Establish `hdet : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹).det = 1 / 2 * ((Matrix.of h).det)⁻¹`. Rewrite using `[Matrix.det_mul, Matrix.det_diagonal, hdi, Fin.prod_univ_two]`. Simplify using the standard rewrite rules. Establish `hpos : 0 < (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹).det`. Rewrite using `[hdet]`.

Use `inv_pos.mpr hΔ` as an intermediate fact. Check the signs of the components of the expression. Establish `m00 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 0 = 1 / 2 * (((Matrix.of h).det)⁻¹ * h 1 1)`. Rewrite using `[Matrix.diagonal_mul, i00]`. Simplify using the standard rewrite rules.

Establish `m01 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 1 = 1 / 2 * (-(((Matrix.of h).det)⁻¹ * h 0 1))`. Rewrite using `[Matrix.diagonal_mul, i01]`. Simplify using the standard rewrite rules. Establish `m10 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 0 = -(((Matrix.of h).det)⁻¹ * h 1 0)`. Rewrite using `[Matrix.diagonal_mul, i10]`.

Simplify using the standard rewrite rules. Establish `m11 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 1 = ((Matrix.of h).det)⁻¹ * h 0 0`. Rewrite using `[Matrix.diagonal_mul, i11]`. Simplify using the standard rewrite rules. Establish `e1 : (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 1 : ℝ) : ℂ) - (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 0 : ℝ) : ℂ) * Complex.I = al h / (((Matrix.of h).det : ℝ) : ℂ)`.

Rewrite using `[m11, m10, al]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 1 : ℝ) : ℂ) - (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 0 : ℝ) : ℂ) * Complex.I = -(be h) / (2 * (((Matrix.of h).det : ℝ) : ℂ))`.

Rewrite using `[m01, m00, be]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hq : -2 * (Real.pi : ℂ) * Complex.I * ((-(be h) / (2 * (((Matrix.of h).det : ℝ) : ℂ))) / (al h / (((Matrix.of h).det : ℝ) : ℂ))) = (Real.pi : ℂ) * Complex.I * (be h / al h)`.

Clear the denominators using the available nonvanishing facts. Establish `hre : ((Real.pi : ℂ) * Complex.I * (be h / al h)).re = -(Real.pi * uu h)`. Rewrite using `[← im_ratio h hΔ]`. Simplify using `[Complex.mul_re, Complex.mul_im]`. Establish `hb : 0 ≤ 1 / 2 * ((Matrix.of h).det)⁻¹`.

Use `inv_pos.mpr hΔ` as an intermediate fact. Check the signs of the components of the expression. Unfold `Wm`. Rewrite using `[if_pos hpos, e1, e2, hq, hdet, norm_mul, norm_mul, Complex.norm_real, norm_zpow, Complex.norm_exp, hre, norm_div, Complex.norm_real, Real.norm_of_nonneg hΔ.le, Real.norm_of_nonneg (Real.rpow_nonneg hb _)]`.
-/
theorem norm_Wm (k : ℕ) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    ‖Wm k (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹)‖ =
      (1 / 2 * ((Matrix.of h).det)⁻¹) ^ ((2 * (k : ℝ) - 1) / 2) *
        (‖al h‖ / (Matrix.of h).det) ^ (-(2 * (k : ℤ) - 1)) * Real.exp (-(Real.pi * uu h)) := by
  obtain ⟨i00, i01, i10, i11⟩ := GlobalTheory.CompanionTheory.WeightClosed.inv_entries h
  have hα := al_ne h hΔ
  have hD : (((Matrix.of h).det : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hΔ.ne'
  have hdi : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hdet : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹).det =
      1 / 2 * ((Matrix.of h).det)⁻¹ := by
    rw [Matrix.det_mul, Matrix.det_diagonal, hdi, Fin.prod_univ_two]
    simp
  have hpos : 0 < (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹).det := by
    rw [hdet]
    have := inv_pos.mpr hΔ
    positivity
  have m00 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 0 =
      1 / 2 * (((Matrix.of h).det)⁻¹ * h 1 1) := by
    rw [Matrix.diagonal_mul, i00]; simp
  have m01 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 1 =
      1 / 2 * (-(((Matrix.of h).det)⁻¹ * h 0 1)) := by
    rw [Matrix.diagonal_mul, i01]; simp
  have m10 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 0 =
      -(((Matrix.of h).det)⁻¹ * h 1 0) := by
    rw [Matrix.diagonal_mul, i10]; simp
  have m11 : (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 1 =
      ((Matrix.of h).det)⁻¹ * h 0 0 := by
    rw [Matrix.diagonal_mul, i11]; simp
  have e1 : (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 1 : ℝ) : ℂ) -
      (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 1 0 : ℝ) : ℂ) * Complex.I =
      al h / (((Matrix.of h).det : ℝ) : ℂ) := by
    rw [m11, m10, al]
    push_cast
    field_simp
    ring
  have e2 : (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 1 : ℝ) : ℂ) -
      (((Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹) 0 0 : ℝ) : ℂ) * Complex.I =
      -(be h) / (2 * (((Matrix.of h).det : ℝ) : ℂ)) := by
    rw [m01, m00, be]
    push_cast
    field_simp
    ring
  have hq : -2 * (Real.pi : ℂ) * Complex.I *
      ((-(be h) / (2 * (((Matrix.of h).det : ℝ) : ℂ))) / (al h / (((Matrix.of h).det : ℝ) : ℂ))) =
      (Real.pi : ℂ) * Complex.I * (be h / al h) := by
    field_simp
  have hre : ((Real.pi : ℂ) * Complex.I * (be h / al h)).re = -(Real.pi * uu h) := by
    rw [← im_ratio h hΔ]
    simp [Complex.mul_re, Complex.mul_im]
  have hb : 0 ≤ 1 / 2 * ((Matrix.of h).det)⁻¹ := by
    have := inv_pos.mpr hΔ
    positivity
  unfold Wm
  rw [if_pos hpos, e1, e2, hq, hdet, norm_mul, norm_mul, Complex.norm_real, norm_zpow,
    Complex.norm_exp, hre, norm_div, Complex.norm_real, Real.norm_of_nonneg hΔ.le,
    Real.norm_of_nonneg (Real.rpow_nonneg hb _)]

/- English proof (translation)
Establish `hp` using `Real.pi_gt_three`. Establish `hx : 0 ≤ Real.pi * u` using `by positivity`. Establish `h1` using `Real.quadratic_le_exp_of_nonneg hx`. Establish `h2 : 3 * u ≤ Real.pi * u` using `by nlinarith`. Establish `h3 : 9 * u ^ 2 ≤ (Real.pi * u) ^ 2` using `by nlinarith [mul_nonneg hu hu]`.

Use polynomial arithmetic with `[mul_nonneg hu hu]`.
-/
theorem sq_le_exp (u : ℝ) (hu : 0 ≤ u) : (1 + u) ^ 2 ≤ Real.exp (Real.pi * u) := by
  have hp := Real.pi_gt_three
  have hx : 0 ≤ Real.pi * u := by positivity
  have h1 := Real.quadratic_le_exp_of_nonneg hx
  have h2 : 3 * u ≤ Real.pi * u := by nlinarith
  have h3 : 9 * u ^ 2 ≤ (Real.pi * u) ^ 2 := by nlinarith [mul_nonneg hu hu]
  nlinarith [mul_nonneg hu hu]

/- English proof (translation)
Establish `hreal` using `GlobalTheory.CompanionTheory.WeightClosed.real_factor k (by omega) _ hΔ`. Rewrite using `[norm_Wm k h hΔ, abs_of_pos hΔ]`. Use `set D := (Matrix.of h).det with hDdef`. Establish `hhalf : (0 : ℝ) ≤ 1 / 2` using `by norm_num`. Establish `hinv : 0 ≤ D⁻¹` using `(inv_pos.mpr hΔ).le`.

Establish `h32 : D ^ (-(3 : ℝ) / 2) = D ^ (-(1 : ℝ) / 2) * D⁻¹`. Rewrite using `[← Real.rpow_neg_one D, ← Real.rpow_add hΔ]`. Evaluate the numerical expressions. Establish `h2 : (2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2) * (1 / 2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2) = 1`. Rewrite using `[← Real.mul_rpow (by norm_num) hhalf]`.

Evaluate the numerical expressions. Rewrite using `[Real.mul_rpow hhalf hinv, h32, div_zpow, zpow_neg D, div_inv_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem scaled (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    (2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2) *
        (‖Wm k (Matrix.diagonal ![(1 / 2 : ℝ), 1] * (Matrix.of h)⁻¹)‖ *
          |(Matrix.of h).det| ^ (-(3 : ℝ) / 2)) =
      (Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) *
        Real.exp (-(Real.pi * uu h)) * ((Matrix.of h).det)⁻¹ := by
  have hreal := GlobalTheory.CompanionTheory.WeightClosed.real_factor k (by omega) _ hΔ
  rw [norm_Wm k h hΔ, abs_of_pos hΔ]
  set D := (Matrix.of h).det with hDdef
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hinv : 0 ≤ D⁻¹ := (inv_pos.mpr hΔ).le
  have h32 : D ^ (-(3 : ℝ) / 2) = D ^ (-(1 : ℝ) / 2) * D⁻¹ := by
    rw [← Real.rpow_neg_one D, ← Real.rpow_add hΔ]
    norm_num
  have h2 : (2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2) * (1 / 2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2) = 1 := by
    rw [← Real.mul_rpow (by norm_num) hhalf]
    norm_num
  rw [Real.mul_rpow hhalf hinv, h32, div_zpow, zpow_neg D, div_inv_eq_mul]
  calc _ = ((2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2) * (1 / 2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2)) *
        (D⁻¹ ^ ((2 * (k : ℝ) - 1) / 2) * D ^ (-(1 : ℝ) / 2) * D ^ (2 * (k : ℤ) - 1)) *
        (‖al h‖ ^ (-(2 * (k : ℤ) - 1)) * Real.exp (-(Real.pi * uu h)) * D⁻¹) := by ring
    _ = _ := by rw [h2, hreal]; ring

end GlobalTheory.CompanionTheory.DInt2.WMaj

open GlobalTheory.CompanionTheory.DInt2.WMaj in

/- English proof (translation)
Introduce `k hk`. Use `⟨(2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2), fun N h hΔ => ?_⟩` and prove the remaining obligations. Establish `hsc` using `scaled k hk h hΔ`. Establish `hu` using `uu_pos h hΔ`. Establish `hden : 0 < (1 + ‖h‖) ^ N * (1 + ‖Ad3.LR.B.eta h‖) ^ N` using `by positivity`.

Establish `hA : 0 < ‖al h‖` using `norm_pos_iff.mpr (al_ne h hΔ)`. Establish `hexp : (1 + uu h) ^ 2 * Real.exp (-(2 * Real.pi * uu h)) ≤ Real.exp (-(Real.pi * uu h))`. Establish `e : Real.exp (-(2 * Real.pi * uu h)) = Real.exp (-(Real.pi * uu h)) * Real.exp (-(Real.pi * uu h))`. Rewrite using `[← Real.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `e' : Real.exp (Real.pi * uu h) * Real.exp (-(Real.pi * uu h)) = 1`. Rewrite using `[← Real.exp_add]`. Simplify using the standard rewrite rules. Use `sq_le_exp _ hu.le` as an intermediate fact.

Establish `hp` using `Real.exp_pos (-(Real.pi * uu h))`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Unfold `Ad3.LR.B.maj`. Rewrite using `[abs_one, one_mul, ← mul_div_assoc, hsc, norm_weight_closed_form k hk h hΔ, abs_of_pos hΔ]`.

Apply `div_le_div_of_nonneg_right _ hden.le` to reduce the goal to its premises. Establish `hc : 0 ≤ (Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) * ((Matrix.of h).det)⁻¹`. Use `inv_pos.mpr hΔ` as an intermediate fact. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GlobalTheory.CompanionTheory.DInt2.WMaj.main : ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, ∀ (N : ℕ) (h : M22),
    0 < (Matrix.of h).det →
    (1 + uu h) ^ 2 * ‖w0 k h‖ * |(Matrix.of h).det|⁻¹ /
        ((1 + ‖h‖) ^ N * (1 + ‖Ad3.LR.B.eta h‖) ^ N) ≤ C * Ad3.LR.B.maj k N (1 / 2) 1 h := by
  intro k hk
  refine ⟨(2 : ℝ) ^ ((2 * (k : ℝ) - 1) / 2), fun N h hΔ => ?_⟩
  have hsc := scaled k hk h hΔ
  have hu := uu_pos h hΔ
  have hden : 0 < (1 + ‖h‖) ^ N * (1 + ‖Ad3.LR.B.eta h‖) ^ N := by positivity
  have hA : 0 < ‖al h‖ := norm_pos_iff.mpr (al_ne h hΔ)
  have hexp : (1 + uu h) ^ 2 * Real.exp (-(2 * Real.pi * uu h)) ≤ Real.exp (-(Real.pi * uu h)) := by
    have e : Real.exp (-(2 * Real.pi * uu h)) =
        Real.exp (-(Real.pi * uu h)) * Real.exp (-(Real.pi * uu h)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e' : Real.exp (Real.pi * uu h) * Real.exp (-(Real.pi * uu h)) = 1 := by
      rw [← Real.exp_add]; simp
    have := sq_le_exp _ hu.le
    have hp := Real.exp_pos (-(Real.pi * uu h))
    rw [e]
    calc (1 + uu h) ^ 2 * (Real.exp (-(Real.pi * uu h)) * Real.exp (-(Real.pi * uu h)))
        ≤ Real.exp (Real.pi * uu h) * (Real.exp (-(Real.pi * uu h)) * Real.exp (-(Real.pi * uu h))) := by
          gcongr
      _ = Real.exp (-(Real.pi * uu h)) := by rw [← mul_assoc, e', one_mul]
  unfold Ad3.LR.B.maj
  rw [abs_one, one_mul, ← mul_div_assoc, hsc, norm_weight_closed_form k hk h hΔ, abs_of_pos hΔ]
  apply div_le_div_of_nonneg_right _ hden.le
  have hc : 0 ≤ (Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) *
      ((Matrix.of h).det)⁻¹ := by
    have := inv_pos.mpr hΔ
    positivity
  calc _ = ((Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) * ((Matrix.of h).det)⁻¹) *
        ((1 + uu h) ^ 2 * Real.exp (-(2 * Real.pi * uu h))) := by ring
    _ ≤ ((Matrix.of h).det ^ (k - 1) * ‖al h‖ ^ (-(2 * (k : ℤ) - 1)) * ((Matrix.of h).det)⁻¹) *
        Real.exp (-(Real.pi * uu h)) := mul_le_mul_of_nonneg_left hexp hc
    _ = _ := by ring
