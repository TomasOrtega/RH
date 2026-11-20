import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfEssentiallyEtaleLocalAlgebras
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.flat_of_essEtale` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlatOfEssentiallyEtaleLocalAlgebras.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.flat_of_essentiallyEtale_local_algebras : ∀ (R L₁ L₂ : Type) [CommRing R] [CommRing L₁] [CommRing L₂] [Algebra R L₁] [Algebra R L₂] [Algebra L₁ L₂] [IsScalarTower R L₁ L₂], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₁)) → (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₂)) → Module.Flat L₁ L₂ := by
  first | exact @GlobalTheory.flat_of_essEtale | exact GlobalTheory.flat_of_essEtale | (intros; apply GlobalTheory.flat_of_essEtale <;> assumption)
