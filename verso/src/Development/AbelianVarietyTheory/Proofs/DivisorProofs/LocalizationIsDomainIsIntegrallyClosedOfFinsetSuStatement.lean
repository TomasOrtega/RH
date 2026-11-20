import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationIsDomainIsIntegrallyClosedOfFinsetSu
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalizationIsDomainIsIntegrallyClosedOfFinsetSu.lean&line=191#L191)
-/
theorem _root_.GlobalTheory.T.isDomain_isIntegrallyClosed_atPrime_of_finset_subrings : ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring | exact GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring | (intros; apply GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring <;> assumption)
