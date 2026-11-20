import Mathlib

noncomputable section

open MeasureTheory Complex

namespace PositivityTheory.Rg.Sw.WR.G.GB

/- English proof (translation)
Establish `h` using `Complex.volume_preserving_equiv_real_prod.symm`. Rewrite using `[← h.integral_comp' (g := fun z : ℂ => cexp (-(w * ((‖z‖ ^ 2 : ℝ) : ℂ))))]`. Establish `e : ∀ p : ℝ × ℝ, cexp (-(w * ((‖measurableEquivRealProd.symm p‖ ^ 2 : ℝ) : ℂ))) = cexp (-w * (p.1 : ℂ) ^ 2) * cexp (-w * (p.2 : ℂ) ^ 2)`. Introduce `p`. Rewrite using `[← Complex.exp_add]`.

Use `congr 1`. Rewrite using `[measurableEquivRealProd_symm_apply, Complex.sq_norm, Complex.normSq_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e]`.

Rewrite using `[show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl, integral_prod_mul (fun x : ℝ => cexp (-w * (x : ℂ) ^ 2)) (fun x : ℝ => cexp (-w * (x : ℂ) ^ 2)), integral_gaussian_complex hw]`. Establish `hne : (Real.pi : ℂ) / w ≠ 0`. Establish `: w ≠ 0` using `by intro h0; rw [h0] at hw; simp at hw`. Conclude with `div_ne_zero (by exact_mod_cast Real.pi_ne_zero) this`. Rewrite using `[← Complex.cpow_add _ _ hne]`.

Evaluate the numerical expressions.
-/
theorem gauss_one (w : ℂ) (hw : 0 < w.re) :
    ∫ z : ℂ, cexp (-(w * ((‖z‖ ^ 2 : ℝ) : ℂ))) = (Real.pi : ℂ) / w := by
  have h := Complex.volume_preserving_equiv_real_prod.symm
  rw [← h.integral_comp' (g := fun z : ℂ => cexp (-(w * ((‖z‖ ^ 2 : ℝ) : ℂ))))]
  have e : ∀ p : ℝ × ℝ, cexp (-(w * ((‖measurableEquivRealProd.symm p‖ ^ 2 : ℝ) : ℂ))) =
      cexp (-w * (p.1 : ℂ) ^ 2) * cexp (-w * (p.2 : ℂ) ^ 2) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    rw [measurableEquivRealProd_symm_apply, Complex.sq_norm, Complex.normSq_apply]
    push_cast
    ring
  simp_rw [e]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    integral_prod_mul (fun x : ℝ => cexp (-w * (x : ℂ) ^ 2)) (fun x : ℝ => cexp (-w * (x : ℂ) ^ 2)),
    integral_gaussian_complex hw]
  have hne : (Real.pi : ℂ) / w ≠ 0 := by
    have : w ≠ 0 := by intro h0; rw [h0] at hw; simp at hw
    exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) this
  rw [← Complex.cpow_add _ _ hne]
  norm_num

/- English proof (translation)
Establish `e : ∀ r : Fin n → ℂ, cexp (-∑ k, d k * ((‖r k‖ ^ 2 : ℝ) : ℂ)) = ∏ k, cexp (-(d k * ((‖r k‖ ^ 2 : ℝ) : ℂ)))`. Introduce `r`. Rewrite using `[← Complex.exp_sum, Finset.sum_neg_distrib]`. Repeatedly rewrite using `[e]`. Rewrite using `[integral_fintype_prod_volume_eq_prod (fun k (z : ℂ) => cexp (-(d k * ((‖z‖ ^ 2 : ℝ) : ℂ))))]`.

Conclude with `Finset.prod_congr rfl fun k _ => gauss_one (d k) (hd k)`.
-/
theorem gauss_diag {n : ℕ} (d : Fin n → ℂ) (hd : ∀ k, 0 < (d k).re) :
    ∫ r : Fin n → ℂ, cexp (-∑ k, d k * ((‖r k‖ ^ 2 : ℝ) : ℂ)) = ∏ k, (Real.pi : ℂ) / d k := by
  have e : ∀ r : Fin n → ℂ, cexp (-∑ k, d k * ((‖r k‖ ^ 2 : ℝ) : ℂ)) =
      ∏ k, cexp (-(d k * ((‖r k‖ ^ 2 : ℝ) : ℂ))) := by
    intro r
    rw [← Complex.exp_sum, Finset.sum_neg_distrib]
  simp_rw [e]
  rw [integral_fintype_prod_volume_eq_prod (fun k (z : ℂ) => cexp (-(d k * ((‖z‖ ^ 2 : ℝ) : ℂ))))]
  exact Finset.prod_congr rfl fun k _ => gauss_one (d k) (hd k)

end PositivityTheory.Rg.Sw.WR.G.GB
