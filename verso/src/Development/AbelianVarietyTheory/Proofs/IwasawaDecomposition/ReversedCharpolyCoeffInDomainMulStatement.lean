import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReversedCharpolyCoeffInDomainMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NormalDescent.normCoeff_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FReversedCharpolyCoeffInDomainMul.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.reversedCharpolyCoeffInDomain_mul : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (u : A) (b : B) (k : ℕ), normCoeff φ hφ (φ u * b) k = u ^ k * normCoeff φ hφ b k := by
  first | exact @GlobalTheory.NormalDescent.normCoeff_mul | exact GlobalTheory.NormalDescent.normCoeff_mul | (intros; apply GlobalTheory.NormalDescent.normCoeff_mul <;> assumption)
