import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffMatrixFamilyBilateralSubstitutionMonomialCo
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FCoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic : ∀ {ι : Type} {N n : ℕ} (k k' : ι × Fin N × Fin n →₀ ℕ), Continuous (fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) => MvPolynomial.coeff k' (GlobalTheory.CompactHowe.substF p.1 p.2 (MvPolynomial.monomial k 1))) ∧ ∀ (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ), (∀ i a b, IsAlgebraic ℚ (h i a b)) → (∀ i a b, IsAlgebraic ℚ (g i a b)) → IsAlgebraic ℚ (MvPolynomial.coeff k' (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1))) := by
  first | exact @GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | exact GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | (intros; apply GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic <;> assumption)
