import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffCoboundaryOneAdditiveEqZeroOfDegree
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoeffCoboundaryOneAdditiveEqZeroOfDegree.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.coeff_coboundaryOne_additive_eq_zero_of_degree : ∀ (R : Type) [CommRing R] (d N : ℕ) (b : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree = N → coeff α b = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → coeff γ (cob1 (addLaw R d) b) = 0 := by
  first | exact @GlobalTheory.Katz.coeff_cob1_addLaw_eq_zero_of_degree_eq | exact GlobalTheory.Katz.coeff_cob1_addLaw_eq_zero_of_degree_eq | (intros; apply GlobalTheory.Katz.coeff_cob1_addLaw_eq_zero_of_degree_eq <;> assumption)
