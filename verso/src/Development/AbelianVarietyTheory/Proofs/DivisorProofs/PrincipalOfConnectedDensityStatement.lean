import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalOfConnectedDensity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrincipalOfConnectedDensity.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.principal_of_connected_density : ConnSt → GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ → DensSt → PrincSt := by
  first | exact @GlobalTheory.FlatModel.princSt_of_connSt_propZ_densSt | exact GlobalTheory.FlatModel.princSt_of_connSt_propZ_densSt | (intros; apply GlobalTheory.FlatModel.princSt_of_connSt_propZ_densSt <;> assumption)
