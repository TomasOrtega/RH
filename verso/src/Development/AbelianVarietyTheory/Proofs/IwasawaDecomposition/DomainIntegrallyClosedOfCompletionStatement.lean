import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomainIntegrallyClosedOfCompletion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDomainIntegrallyClosedOfCompletion.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.domain_integrally_closed_of_completion : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T], IsDomain (AdicCompletion (maximalIdeal T) T) → IsIntegrallyClosed (AdicCompletion (maximalIdeal T) T) → IsDomain T ∧ IsIntegrallyClosed T := by
  first | exact @GlobalTheory.isDomain_isIntegrallyClosed_of_adicCompletion | exact GlobalTheory.isDomain_isIntegrallyClosed_of_adicCompletion | (intros; apply GlobalTheory.isDomain_isIntegrallyClosed_of_adicCompletion <;> assumption)
