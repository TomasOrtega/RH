import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainPointsOmegaStable
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast
open GlobalTheory GlobalTheory.ChainPts
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChainPointsOmegaStable.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.chain_points_omega_stable : GlobalTheory.ChainPts.ReadsOmSt := by
  first | exact @GlobalTheory.ChainPts.readsOmSt | exact GlobalTheory.ChainPts.readsOmSt | (intros; apply GlobalTheory.ChainPts.readsOmSt <;> assumption)
