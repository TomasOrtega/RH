import ReciprocityTheory.ThetaSummability.TailSumEstimates.ConeChange

namespace ReciprocityTheory.ThetaSummability.Est

open MeasureTheory Finset Real

variable {r : ℕ}

/- English proof (translation)
Simplify using `only [tailSum, partialSum, Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sum_mul_tailSum (s y : Fin r → ℝ) :
    ∑ i, s i * tailSum y i = ∑ k, partialSum s k * y k := by
  simp only [tailSum, partialSum, Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `y`. Rewrite using `[sum_mul_tailSum, Real.exp_sum]`.
-/
theorem exp_sum_mul_tailSum_eq (s : Fin r → ℝ) :
    (fun y : Fin r → ℝ => exp (∑ i, s i * tailSum y i)) =
      fun y => ∏ k, (fun (k : Fin r) (t : ℝ) => exp (partialSum s k * t)) k (y k) := by
  funext y
  rw [sum_mul_tailSum, Real.exp_sum]

/- English proof (translation)
Rewrite using `[integrableOn_logCone_iff]`. Use `show IntegrableOn (fun y : Fin r → ℝ => exp (∑ i, s i * tailSum y i)) (lowerBox r c)`. Rewrite using `[exp_sum_mul_tailSum_eq, IntegrableOn, lowerBox, volume_pi, Measure.restrict_pi_pi]`. Use `Integrable.fintype_prod (E := ℝ) (f := fun (k : Fin r) (t : ℝ) => exp (partialSum s k * t)) (μ := fun _ => volume.restrict (Set.Ici c)) fun k => ?_` and prove the remaining obligations. Use `show IntegrableOn (fun t : ℝ => exp (partialSum s k * t)) (Set.Ici c)`.

Rewrite using `[integrableOn_Ici_iff_integrableOn_Ioi]`. Conclude with `integrableOn_exp_mul_Ioi (hs k) c`.
-/
theorem integrableOn_exp_logCone (c : ℝ) {s : Fin r → ℝ} (hs : ∀ k, partialSum s k < 0) :
    IntegrableOn (fun x => exp (∑ i, s i * x i)) (logCone r c) := by
  rw [integrableOn_logCone_iff]
  show IntegrableOn (fun y : Fin r → ℝ => exp (∑ i, s i * tailSum y i)) (lowerBox r c)
  rw [exp_sum_mul_tailSum_eq, IntegrableOn, lowerBox, volume_pi, Measure.restrict_pi_pi]
  refine Integrable.fintype_prod (E := ℝ) (f := fun (k : Fin r) (t : ℝ) => exp (partialSum s k * t))
    (μ := fun _ => volume.restrict (Set.Ici c)) fun k => ?_
  show IntegrableOn (fun t : ℝ => exp (partialSum s k * t)) (Set.Ici c)
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_mul_Ioi (hs k) c

/- English proof (translation)
Rewrite using `[setIntegral_logCone]`. Use `show ∫ y in lowerBox r c, (fun y : Fin r → ℝ => exp (∑ i, s i * tailSum y i)) y = _`. Rewrite using `[exp_sum_mul_tailSum_eq, lowerBox, volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod (E := fun _ => ℝ) (fun (k : Fin r) (t : ℝ) => exp (partialSum s k * t))]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (hs k), neg_div, div_neg]`.
-/
theorem integral_exp_logCone (c : ℝ) {s : Fin r → ℝ} (hs : ∀ k, partialSum s k < 0) :
    ∫ x in logCone r c, exp (∑ i, s i * x i) =
      ∏ k, exp (partialSum s k * c) / (-partialSum s k) := by
  rw [setIntegral_logCone]
  show ∫ y in lowerBox r c, (fun y : Fin r → ℝ => exp (∑ i, s i * tailSum y i)) y = _
  rw [exp_sum_mul_tailSum_eq, lowerBox, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (E := fun _ => ℝ)
      (fun (k : Fin r) (t : ℝ) => exp (partialSum s k * t))]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (hs k), neg_div, div_neg]

end ReciprocityTheory.ThetaSummability.Est
