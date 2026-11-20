import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogIntegralUnitsSubgroupExpHomProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLogIntegralUnitsSubgroupExpHomProof.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.logIntegralUnitsSubgroupExpHom_proof : UnitSt := by
  first | exact @GlobalTheory.IsoTriv.unitSt | exact GlobalTheory.IsoTriv.unitSt | (intros; apply GlobalTheory.IsoTriv.unitSt <;> assumption)
