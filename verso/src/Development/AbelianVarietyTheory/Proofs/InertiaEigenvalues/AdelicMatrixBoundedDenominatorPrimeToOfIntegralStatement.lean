import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixBoundedDenominatorPrimeToOfIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BndMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StdAtPrime.bnd_of_integral_over_prime` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAdelicMatrixBoundedDenominatorPrimeToOfIntegral.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)), (∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → ∀ i j, Valued.v ((A i j) Q) ≤ 1) → GlobalTheory.StdAtPrime.Bnd p A := by
  first | exact @GlobalTheory.StdAtPrime.bnd_of_integral_over_prime | exact GlobalTheory.StdAtPrime.bnd_of_integral_over_prime | (intros; apply GlobalTheory.StdAtPrime.bnd_of_integral_over_prime <;> assumption)
