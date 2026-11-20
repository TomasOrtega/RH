import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntegrallyClosedOfReducedQuotientLocalization

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIsIntegrallyClosedOfReducedQuotientLocalization.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.isIntegrallyClosed_of_reduced_quotient_localization : ∀ (A : Type) [CommRing A] [IsDomain A] (t : A), t ≠ 0 → IsReduced (A ⧸ Ideal.span {t}) → IsIntegrallyClosed (Localization.Away t) → IsIntegrallyClosed A := by
  first | exact @GlobalTheory.CompanionTheory.IntClosedAway.isIntegrallyClosed_of_away | exact GlobalTheory.CompanionTheory.IntClosedAway.isIntegrallyClosed_of_away | (intros; apply GlobalTheory.CompanionTheory.IntClosedAway.isIntegrallyClosed_of_away <;> assumption)
