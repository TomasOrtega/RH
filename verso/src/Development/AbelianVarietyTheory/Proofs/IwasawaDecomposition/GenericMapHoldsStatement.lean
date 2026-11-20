import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericMapHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GenMap.genMapSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FGenericMapHolds.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.generic_map_holds : GenMapSt := by
  first | exact @GlobalTheory.GenMap.genMapSt | exact GlobalTheory.GenMap.genMapSt | (intros; apply GlobalTheory.GenMap.genMapSt <;> assumption)
