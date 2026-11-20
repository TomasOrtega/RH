import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionLieAlgebraOfPrimeIdempotentApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLimitActionLieAlgebraOfPrimeIdempotentApprox.lean&line=144#L144)
-/
theorem _root_.GlobalTheory.T.limitActionLieAlgebra_of_primeIdempotentApprox : EpsSt → LimActSt := by
  first | exact @GlobalTheory.IsoTriv.limActSt_of_epsSt | exact GlobalTheory.IsoTriv.limActSt_of_epsSt | (intros; apply GlobalTheory.IsoTriv.limActSt_of_epsSt <;> assumption)
