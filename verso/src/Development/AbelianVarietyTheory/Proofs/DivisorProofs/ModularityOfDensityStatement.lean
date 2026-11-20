import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularityOfDensity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatModel.modSt_of_densSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FModularityOfDensity.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.modularity_of_density : DensSt → ModSt := by
  first | exact @GlobalTheory.FlatModel.modSt_of_densSt | exact GlobalTheory.FlatModel.modSt_of_densSt | (intros; apply GlobalTheory.FlatModel.modSt_of_densSt <;> assumption)
