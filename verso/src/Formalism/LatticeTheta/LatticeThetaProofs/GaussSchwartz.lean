import Formalism.LatticeTheta.LatticeSummableDecay

open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/- English proof (translation)
Use function extensionality and compare the values at `v`. Rewrite using `[Complex.ofReal_exp]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma gauss_fun_eq (t : ℝ) :
    (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) =
      fun v : V => cexp (-((Real.pi * t : ℝ) : ℂ) * (‖v‖ : ℂ) ^ 2) := by
  funext v
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/- English proof (translation)
Conclude with `Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))`.
-/
lemma gauss_continuous (t : ℝ) :
    Continuous (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) := by
  exact Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))

/- English proof (translation)
Establish `ha : -Real.pi * t < 0` using `by nlinarith [Real.pi_pos]`. Establish `h1` using `((rexp_neg_quadratic_isLittleO_rpow_atTop ha 0 (-b)).comp_tendsto (tendsto_norm_cocompact_atTop (E := V))).isBigO`. Use `Asymptotics.IsBigO.of_norm_left ?_` and prove the remaining obligations. Use `h1.congr_left fun v => ?_` and prove the remaining obligations. Simplify using `only [Function.comp]`.

Use `first`. Consider the case `rw [zero_mul, add_zero, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]`. Consider the case `simp [Real.abs_exp]`.
-/
lemma gauss_decay (t : ℝ) (ht : 0 < t) (b : ℝ) :
    (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) =O[cocompact V]
      (fun v => ‖v‖ ^ (-b)) := by
  have ha : -Real.pi * t < 0 := by nlinarith [Real.pi_pos]
  have h1 := ((rexp_neg_quadratic_isLittleO_rpow_atTop ha 0 (-b)).comp_tendsto
    (tendsto_norm_cocompact_atTop (E := V))).isBigO
  refine Asymptotics.IsBigO.of_norm_left ?_
  refine h1.congr_left fun v => ?_
  simp only [Function.comp]
  first
    | rw [zero_mul, add_zero, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    | simp [Real.abs_exp]

/- English proof (translation)
Establish `hb : 0 < (((Real.pi * t : ℝ) : ℂ)).re`. Rewrite using `[Complex.ofReal_re]`. Conclude with `mul_pos Real.pi_pos ht`. Rewrite using `[gauss_fun_eq, fourier_gaussian_innerProductSpace hb w]`. Establish `hπ : (Real.pi : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr Real.pi_ne_zero`.

Establish `ht' : (t : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr ht.ne'`. Establish `e1 : (Real.pi : ℂ) / ((Real.pi * t : ℝ) : ℂ) = ((t⁻¹ : ℝ) : ℂ)`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `e2 : ((t⁻¹ : ℝ) : ℂ) ^ ((Module.finrank ℝ V : ℂ) / 2) = ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ)`.

Rewrite using `[show ((Module.finrank ℝ V : ℂ) / 2) = (((Module.finrank ℝ V : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (inv_nonneg.mpr ht.le), Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_div]`. Rewrite using `[e1, e2, Complex.ofReal_exp]`. Use `congr 2`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
lemma gauss_fourier (t : ℝ) (ht : 0 < t) (w : V) :
    (𝓕 (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) : V → ℂ) w =
      ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) * (Real.exp (-Real.pi * ‖w‖ ^ 2 / t) : ℂ) := by
  have hb : 0 < (((Real.pi * t : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]; exact mul_pos Real.pi_pos ht
  rw [gauss_fun_eq, fourier_gaussian_innerProductSpace hb w]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have e1 : (Real.pi : ℂ) / ((Real.pi * t : ℝ) : ℂ) = ((t⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp
  have e2 : ((t⁻¹ : ℝ) : ℂ) ^ ((Module.finrank ℝ V : ℂ) / 2) =
      ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show ((Module.finrank ℝ V : ℂ) / 2) = (((Module.finrank ℝ V : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (inv_nonneg.mpr ht.le), Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_div]
  rw [e1, e2, Complex.ofReal_exp]
  congr 2
  push_cast
  field_simp

/- English proof (translation)
Introduce `t ht` and use `⟨gauss_continuous V t, gauss_decay V t ht, gauss_fourier V t ht⟩`.
-/
theorem gaussian_fourier_transform : GaussFourier V := fun t ht => ⟨gauss_continuous V t, gauss_decay V t ht, gauss_fourier V t ht⟩

/- English proof (translation)
Introduce `f b`. Use `⟨f.isBigO_cocompact_rpow (-b), ?_⟩` and prove the remaining obligations. Establish `h` using `(FourierTransform.fourier f : 𝓢(V, ℂ)).isBigO_cocompact_rpow (-b)`. Rewrite `h` using `[SchwartzMap.fourier_coe]`. Then use the resulting hypothesis.
-/
theorem schwartz_decay_gaussian : SchwartzDecay V := by
  intro f b
  refine ⟨f.isBigO_cocompact_rpow (-b), ?_⟩
  have h := (FourierTransform.fourier f : 𝓢(V, ℂ)).isBigO_cocompact_rpow (-b)
  rwa [SchwartzMap.fourier_coe] at h

/- English proof (translation)
Assemble the required witnesses or components as `⟨gaussian_fourier_transform V, schwartz_decay_gaussian V⟩`.
-/
theorem gaussian_fourier_and_decay : GaussFourier V ∧ SchwartzDecay V := ⟨gaussian_fourier_transform V, schwartz_decay_gaussian V⟩

end Formalism.H
