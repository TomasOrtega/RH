import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleQuotientOfEtalePunctured
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.etale_quotient_of_etale_punctured` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEtaleQuotientOfEtalePunctured.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.etale_quotient_of_etale_punctured' : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A] (f : R) [IsLocalRing (R ⧸ Ideal.span {f})], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ (P : Ideal (R ⧸ Ideal.span {f})) [P.IsPrime], P ≠ maximalIdeal (R ⧸ Ideal.span {f}) → Algebra.Etale (Localization.AtPrime P) (TensorProduct (R ⧸ Ideal.span {f}) (Localization.AtPrime P) (A ⧸ (Ideal.span {f}).map (algebraMap R A))) := by
  first | exact @GlobalTheory.etale_quotient_of_etale_punctured | exact GlobalTheory.etale_quotient_of_etale_punctured | (intros; apply GlobalTheory.etale_quotient_of_etale_punctured <;> assumption)
