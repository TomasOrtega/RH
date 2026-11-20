import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SphericalTransitiveOfLevi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists | exact GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists | (intros; apply GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.spherical_transitive_of_levi : LeviExists → SphTrans := by
  first | exact @GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists | exact GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists | (intros; apply GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists <;> assumption)
