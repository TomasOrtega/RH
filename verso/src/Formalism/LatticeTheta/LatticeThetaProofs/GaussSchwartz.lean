import Formalism.LatticeTheta.LatticeSummableDecay

open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
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
A detailed English derivation is pending.
-/
lemma gauss_continuous (t : ℝ) :
    Continuous (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) := by
  exact Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Treat this case separately. Treat this case separately. A detailed English derivation is pending.
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
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
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
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem gaussian_fourier_transform : GaussFourier V := fun t ht => ⟨gauss_continuous V t, gauss_decay V t ht, gauss_fourier V t ht⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem schwartz_decay_gaussian : SchwartzDecay V := by
  intro f b
  refine ⟨f.isBigO_cocompact_rpow (-b), ?_⟩
  have h := (FourierTransform.fourier f : 𝓢(V, ℂ)).isBigO_cocompact_rpow (-b)
  rwa [SchwartzMap.fourier_coe] at h

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem gaussian_fourier_and_decay : GaussFourier V ∧ SchwartzDecay V := ⟨gaussian_fourier_transform V, schwartz_decay_gaussian V⟩

end Formalism.H
