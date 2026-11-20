import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFanOfToroidalCharts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GenFan.genFanSt_of_toroidalCharts` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FGenericFanOfToroidalCharts.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.generic_fan_of_toroidal_charts : GlobalTheory.Published.ToroidalChartsForFan → GenFanSt := by
  first | exact @GlobalTheory.GenFan.genFanSt_of_toroidalCharts | exact GlobalTheory.GenFan.genFanSt_of_toroidalCharts | (intros; apply GlobalTheory.GenFan.genFanSt_of_toroidalCharts <;> assumption)
