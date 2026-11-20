import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalLocalIsLocalisationOfFiniteOverPolynomialA
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNormalLocalIsLocalisationOfFiniteOverPolynomialA.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.injective_and_isLocalization_of_finite_over_mvPolynomial : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], ∃ (r : ℕ) (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsIntegrallyClosed B) (_ : Algebra (MvPolynomial (Fin r) ℤ) B) (_ : Module.Finite (MvPolynomial (Fin r) ℤ) B) (_ : Algebra B A) (𝔫 : Ideal B) (_ : 𝔫.IsPrime), Function.Injective (algebraMap (MvPolynomial (Fin r) ℤ) B) ∧ IsLocalization.AtPrime A 𝔫 := by
  first | exact @GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial | exact GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial | (intros; apply GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial <;> assumption)
