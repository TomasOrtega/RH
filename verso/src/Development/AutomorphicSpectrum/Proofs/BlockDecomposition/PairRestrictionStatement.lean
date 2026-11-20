import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairRestriction
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.EGlue.pairRestrict_holds | exact GlobalTheory.CompanionTheory.EGlue.pairRestrict_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairRestrict_holds <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.pair_restriction : GlobalTheory.CompanionTheory.EGlue.PairRestrict := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.pairRestrict_holds | exact GlobalTheory.CompanionTheory.EGlue.pairRestrict_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairRestrict_holds <;> assumption)
