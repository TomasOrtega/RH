import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeIdempotentApproximationsDVRProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IsoTriv.PrimeIdempotent.epsSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrimeIdempotentApproximationsDVRProof.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.primeIdempotentApproximationsDVR_proof : EpsSt := by
  first | exact @GlobalTheory.IsoTriv.PrimeIdempotent.epsSt | exact GlobalTheory.IsoTriv.PrimeIdempotent.epsSt | (intros; apply GlobalTheory.IsoTriv.PrimeIdempotent.epsSt <;> assumption)
