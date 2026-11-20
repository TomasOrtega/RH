import Mathlib
import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
import Formalism.GaussJetBounds.StatementN
open Formalism.MainNotions Classical

namespace GlobalTheory.Proof.kvalGe_zero_of_integral_jets

/- English proof (translation)
Introduce `Lt _ _ N0 N1 l _ nu Th hTh I m`. Rewrite using `[neg_zero, Real.rpow_zero]`. Unfold `product_zeroth_first_parts.applyAt0`. Rewrite using `[MvPolynomial.coeff_sum]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun μ _ => ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.coeff_monomial]`. Use `split_ifs`. Rewrite using `[mul_assoc, norm_mul]`. Use `mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one ℂ_[l] _) (norm_nonneg _) ?_` and prove the remaining obligations. Establish `h` using `hTh (Finsupp.sumFinsuppEquivProdFinsupp μ).2`.

Unfold `Formalism.DworkPowerSeriesWeights.mfact at h`. Simplify `h` using `[Finsupp.prod, Nat.cast_prod]`. Simplify using the standard rewrite rules.
-/
theorem kvalGe_zero : ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime]
    (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]),
    Formalism.DworkPowerSeriesWeights.JetsIntegral Th → product_zeroth_first_parts.KvalGe N0 N1 l nu Th 0 := by
  intro Lt _ _ N0 N1 l _ nu Th hTh I m
  rw [neg_zero, Real.rpow_zero]
  unfold product_zeroth_first_parts.applyAt0
  rw [MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun μ _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · rw [mul_assoc, norm_mul]
    refine mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one ℂ_[l] _) (norm_nonneg _) ?_
    have h := hTh (Finsupp.sumFinsuppEquivProdFinsupp μ).2
    unfold Formalism.DworkPowerSeriesWeights.mfact at h
    simpa [Finsupp.prod, Nat.cast_prod] using h
  · simp

end GlobalTheory.Proof.kvalGe_zero_of_integral_jets
