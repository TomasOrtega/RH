import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SphericalTransitiveOfLevi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FSphericalTransitiveOfLevi.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.spherical_transitive_of_levi : LeviExists → SphTrans := by
  first | exact @GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists | exact GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists | (intros; apply GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists <;> assumption)
