import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainPointsReadLie
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast
open GlobalTheory GlobalTheory.ChainPts
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.chain_points_read_lie : GlobalTheory.ChainPts.ReadsLieSt := by
  first | exact @GlobalTheory.TriFrame.readsLieSt | exact GlobalTheory.TriFrame.readsLieSt | (intros; apply GlobalTheory.TriFrame.readsLieSt <;> assumption)
