import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.NablaSpanC

noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW

/- English proof (translation)
Introduce `Lt _ _ l _ N0 N1 nu Th B h I m`. Take `⟨c, hc, heq⟩` from `h I`. Rewrite using `[heq]`. Establish `hC : (0 : ℝ) ≤ (l : ℝ) ^ (-B)` using `Real.rpow_nonneg (Nat.cast_nonneg _) _`. Rewrite using `[Finsupp.sum, MvPolynomial.coeff_sum]`.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun J _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, norm_mul]`. Establish `h1 : ‖(Int.castRingHom ℂ_[l]) (MvPolynomial.coeff m (nablaX N0 nu J))‖ ≤ 1`. Simplify using `using IsUltrametricDist.norm_intCast_le_one ℂ_[l] (MvPolynomial.coeff m (nablaX N0 nu J))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem stepBack : StepBack := by
  intro Lt _ _ l _ N0 N1 nu Th B h I m
  obtain ⟨c, hc, heq⟩ := h I
  rw [heq]
  have hC : (0 : ℝ) ≤ (l : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [Finsupp.sum, MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun J _ => ?_
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, norm_mul]
  have h1 : ‖(Int.castRingHom ℂ_[l]) (MvPolynomial.coeff m (nablaX N0 nu J))‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_intCast_le_one ℂ_[l] (MvPolynomial.coeff m (nablaX N0 nu J))
  calc ‖c J‖ * ‖(Int.castRingHom ℂ_[l]) (MvPolynomial.coeff m (nablaX N0 nu J))‖
      ≤ (l : ℝ) ^ (-B) * 1 := mul_le_mul (hc J) h1 (norm_nonneg _) hC
    _ = _ := mul_one _

end GenFrameSpan
