import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow

set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

/- English proof (translation)
Establish `ha` using `norm_nonneg p`. Establish `hb` using `norm_nonneg q`. Establish `h1 : ‖p + q‖ ≤ ‖p‖ + ‖q‖` using `norm_add_le p q`. Establish `h2 : ‖p + q‖ ^ 2 ≤ (‖p‖ + ‖q‖) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) h1 2`. Establish `h3 : 2 * ‖p‖ * ‖q‖ ≤ t * ‖p‖ ^ 2 + 1 / t * ‖q‖ ^ 2`.

Establish `h4 : 0 ≤ (t * ‖p‖ - ‖q‖) ^ 2 / t` using `div_nonneg (sq_nonneg _) ht.le`. Establish `e : (t * ‖p‖ - ‖q‖) ^ 2 / t = t * ‖p‖ ^ 2 - 2 * ‖p‖ * ‖q‖ + 1 / t * ‖q‖ ^ 2`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_add_sq_le_young (p q : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖p + q‖ ^ 2 ≤ (1 + t) * ‖p‖ ^ 2 + (1 + 1 / t) * ‖q‖ ^ 2 := by
  have ha := norm_nonneg p
  have hb := norm_nonneg q
  have h1 : ‖p + q‖ ≤ ‖p‖ + ‖q‖ := norm_add_le p q
  have h2 : ‖p + q‖ ^ 2 ≤ (‖p‖ + ‖q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 2 * ‖p‖ * ‖q‖ ≤ t * ‖p‖ ^ 2 + 1 / t * ‖q‖ ^ 2 := by
    have h4 : 0 ≤ (t * ‖p‖ - ‖q‖) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
    have e : (t * ‖p‖ - ‖q‖) ^ 2 / t = t * ‖p‖ ^ 2 - 2 * ‖p‖ * ‖q‖ + 1 / t * ‖q‖ ^ 2 := by
      field_simp
      ring
    linarith
  nlinarith

/- English proof (translation)
Establish `h1 : ‖∑ l, d l * w l‖ ≤ ∑ l, ‖d l‖ * ‖w l‖` using `(norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))`. Establish `h2` using `Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖d l‖) (fun l => ‖w l‖)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_sum_mul_sq_le {m : ℕ} (d w : Fin m → ℂ) :
    ‖∑ l, d l * w l‖ ^ 2 ≤ (∑ l, ‖d l‖ ^ 2) * ∑ l, ‖w l‖ ^ 2 := by
  have h1 : ‖∑ l, d l * w l‖ ≤ ∑ l, ‖d l‖ * ‖w l‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖d l‖) (fun l => ‖w l‖)
  calc ‖∑ l, d l * w l‖ ^ 2 ≤ (∑ l, ‖d l‖ * ‖w l‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/- English proof (translation)
Establish `hY : ∀ i, (Y *ᵥ w) i = w i + ((Y - 1) *ᵥ w) i`. Introduce `i`. Simplify using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Establish `hc : 0 ≤ 1 + 1 / t`. Use `one_div_pos.mpr ht` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hi : ∀ i, ‖(Y *ᵥ w) i‖ ^ 2 ≤ (1 + t) * ‖w i‖ ^ 2 + (1 + 1 / t) * ((∑ l, ‖(Y - 1) i l‖ ^ 2) * ∑ l, ‖w l‖ ^ 2)`. Introduce `i`. Rewrite using `[hY]`. Use `(norm_add_sq_le_young _ _ ht).trans ?_` and prove the remaining obligations.

Conclude with `add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_sum_mul_sq_le _ _) hc)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_norm_mulVec_sq_le {m : ℕ} (Y : Matrix (Fin m) (Fin m) ℂ) (w : Fin m → ℂ) {t : ℝ} (ht : 0 < t) :
    ∑ i, ‖(Y *ᵥ w) i‖ ^ 2 ≤
      ((1 + t) + (1 + 1 / t) * ∑ i, ∑ l, ‖(Y - 1) i l‖ ^ 2) * ∑ i, ‖w i‖ ^ 2 := by
  have hY : ∀ i, (Y *ᵥ w) i = w i + ((Y - 1) *ᵥ w) i := by
    intro i
    simp [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hc : 0 ≤ 1 + 1 / t := by
    have := one_div_pos.mpr ht
    linarith
  have hi : ∀ i, ‖(Y *ᵥ w) i‖ ^ 2 ≤
      (1 + t) * ‖w i‖ ^ 2 + (1 + 1 / t) * ((∑ l, ‖(Y - 1) i l‖ ^ 2) * ∑ l, ‖w l‖ ^ 2) := by
    intro i
    rw [hY]
    refine (norm_add_sq_le_young _ _ ht).trans ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_sum_mul_sq_le _ _) hc)
  calc ∑ i, ‖(Y *ᵥ w) i‖ ^ 2 ≤ ∑ i, ((1 + t) * ‖w i‖ ^ 2 +
        (1 + 1 / t) * ((∑ l, ‖(Y - 1) i l‖ ^ 2) * ∑ l, ‖w l‖ ^ 2)) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        ring

end Formalism.L2.SG.Pf.Tau
