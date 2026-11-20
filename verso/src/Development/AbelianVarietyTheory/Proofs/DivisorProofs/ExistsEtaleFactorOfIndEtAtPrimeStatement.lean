import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFactorOfIndEtAtPrime
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFibMapAlgebraMap
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsEtaleFactorOfIndEtAtPrime.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.exists_etale_factorization_of_isIndEtale : ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (P : Ideal R) [P.IsPrime]
    (φ : Localization.AtPrime P →+* O), φ.comp (algebraMap R _) = algebraMap R O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (Z : Type) [CommRing Z] [Algebra R Z] [Algebra.FinitePresentation R Z] (g : Z →ₐ[R] O),
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Etale R W)
      (u : Z →ₐ[R] W) (v : W →ₐ[R] O), v.comp u = g := by
  first | exact @GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime | exact GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime | (intros; apply GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime <;> assumption)
