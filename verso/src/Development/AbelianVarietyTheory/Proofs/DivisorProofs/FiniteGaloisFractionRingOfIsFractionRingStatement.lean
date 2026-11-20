import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGaloisFractionRingOfIsFractionRing
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finiteGalois_fractionRing_of_isFractionRing` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteGaloisFractionRingOfIsFractionRing.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.exists_finite_galois_fractionRing_fixing : ∀ (A K L : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra A L], (∀ a : A, algebraMap A L a = algebraMap K L (algebraMap A K a)) → ∃ (_ : Algebra (FractionRing A) L) (_ : IsScalarTower A (FractionRing A) L), FiniteDimensional (FractionRing A) L ∧ IsGalois (FractionRing A) L ∧ ∀ (σ : L ≃ₐ[FractionRing A] L) (x : K), σ (algebraMap K L x) = algebraMap K L x := by
  first | exact @GlobalTheory.finiteGalois_fractionRing_of_isFractionRing | exact GlobalTheory.finiteGalois_fractionRing_of_isFractionRing | (intros; apply GlobalTheory.finiteGalois_fractionRing_of_isFractionRing <;> assumption)
