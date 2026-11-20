import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationIntegralClosureArtinianReducedDomain
import Mathlib
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
/- English proof (citation)
Apply `GlobalTheory.localization_integralClosure_isDomain_isIntegrallyClosed` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalizationIntegralClosureArtinianReducedDomain.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.localization_integralClosure_artinian_reduced_domain : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [IsArtinianRing A] [IsReduced A]
    (Q : Ideal (integralClosure R A)) [Q.IsPrime],
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.localization_integralClosure_isDomain_isIntegrallyClosed | exact GlobalTheory.localization_integralClosure_isDomain_isIntegrallyClosed | (intros; apply GlobalTheory.localization_integralClosure_isDomain_isIntegrallyClosed <;> assumption)
