import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB

noncomputable section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace UpperTheory.Gal.Gen

/- English proof (translation)
Establish `e : a⁻¹ / b⁻¹ = b / a` using `by field_simp`. Rewrite using `[e]`. Establish `h1 : 1 - b / a = (a - b) / a` using `by field_simp`. Establish `h2 : 1 - t * (b / a) = (a - t * b) / a` using `by field_simp`. Rewrite using `[h1, h2]`.

Clear the denominators using the available nonvanishing facts.
-/
private lemma factor_eq {a b t : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) (hat : a - t * b ≠ 0) :
    (a - t * b) / (a - b) * ((1 - a⁻¹ / b⁻¹) / (1 - t * (a⁻¹ / b⁻¹))) = 1 := by
  have e : a⁻¹ / b⁻¹ = b / a := by field_simp
  rw [e]
  have h1 : 1 - b / a = (a - b) / a := by field_simp
  have h2 : 1 - t * (b / a) = (a - t * b) / a := by field_simp
  rw [h1, h2]
  field_simp

/- English proof (translation)
Unfold `half`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one (fun p hp => ?_)` and prove the remaining obligations. Simplify using `only [Pi.inv_apply, Units.val_inv_eq_inv_val]`. Simplify using `only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp`.

Establish `hne : p.1 ≠ p.2` using `hp.ne`. Use `factor_eq (w p.1).ne_zero (w p.2).ne_zero ?_ ?_` and prove the remaining obligations. Introduce `h`. Conclude with `hne (hw (Units.ext (sub_eq_zero.mp h)))`. Introduce `h`.

Establish `h' : (w p.1 : ℂ) = (t : ℂ) * (w p.2 : ℂ)` using `sub_eq_zero.mp h`. Establish `hn'` using `congrArg norm h'`. Rewrite `hn'` using `[norm_mul, hn, hn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma half_cancel (n : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) (w : Fin n → ℂˣ)
    (hw : Function.Injective w) (hn : ∀ i, ‖(w i : ℂ)‖ = 1) :
    (∏ p ∈ prs n, ((w p.1 : ℂ) - (t : ℂ) * (w p.2 : ℂ)) / ((w p.1 : ℂ) - (w p.2 : ℂ))) *
      half (t : ℂ) w⁻¹ = 1 := by
  unfold half
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun p hp => ?_)
  simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
  simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have hne : p.1 ≠ p.2 := hp.ne
  refine factor_eq (w p.1).ne_zero (w p.2).ne_zero ?_ ?_
  · intro h
    exact hne (hw (Units.ext (sub_eq_zero.mp h)))
  · intro h
    have h' : (w p.1 : ℂ) = (t : ℂ) * (w p.2 : ℂ) := sub_eq_zero.mp h
    have hn' := congrArg norm h'
    rw [norm_mul, hn, hn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] at hn'
    linarith

/- English proof (translation)
Introduce `hR hS n t h0 h1 l z hz hn`. Rewrite using `[hR n (t : ℂ) l z hz, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Establish `hw : Function.Injective (z ∘ σ)` using `hz.comp σ.injective`. Establish `hwn : ∀ i, ‖((z ∘ σ) i : ℂ)‖ = 1` using `fun i => hn (σ i)`.

Establish `hc` using `half_cancel n t h0 h1 (z ∘ σ) hw hwn`. Rewrite using `[← hS n (t : ℂ) z σ]`. Unfold `dens`. Simplify using `only [Function.comp_apply] at hc`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rDens_pf : RFormula → DensSymm → RDens := by
  intro hR hS n t h0 h1 l z hz hn
  rw [hR n (t : ℂ) l z hz, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hw : Function.Injective (z ∘ σ) := hz.comp σ.injective
  have hwn : ∀ i, ‖((z ∘ σ) i : ℂ)‖ = 1 := fun i => hn (σ i)
  have hc := half_cancel n t h0 h1 (z ∘ σ) hw hwn
  rw [← hS n (t : ℂ) z σ]
  unfold dens
  simp only [Function.comp_apply] at hc
  calc _ = monomialChar l (z ∘ σ) * half (t : ℂ) (z ∘ σ) * ((∏ p ∈ prs n, ((z (σ p.1) : ℂ) - (t : ℂ) * (z (σ p.2) : ℂ)) / ((z (σ p.1) : ℂ) - (z (σ p.2) : ℂ))) * half (t : ℂ) (z ∘ σ)⁻¹) := by ring
    _ = _ := by rw [hc, mul_one]

end UpperTheory.Gal.Gen

end
