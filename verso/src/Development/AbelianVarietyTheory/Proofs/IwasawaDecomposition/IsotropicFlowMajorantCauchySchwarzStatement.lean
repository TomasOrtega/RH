import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicFlowMajorantCauchySchwarz
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspFrom.flowMajSt_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsotropicFlowMajorantCauchySchwarz.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.isotropicFlow_majorant_cauchySchwarz : FlowMajSt := by
  first | exact @GlobalTheory.CuspFrom.flowMajSt_holds | exact GlobalTheory.CuspFrom.flowMajSt_holds | (intros; apply GlobalTheory.CuspFrom.flowMajSt_holds <;> assumption)
