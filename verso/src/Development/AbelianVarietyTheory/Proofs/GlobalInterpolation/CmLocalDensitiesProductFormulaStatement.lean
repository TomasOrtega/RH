import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmLocalDensitiesProductFormula
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Proof.cm_localDensities_productFormula.densityProduct` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FCmLocalDensitiesProductFormula.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.cm_localDensities_productFormula : GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.DensityProduct := by
  first | exact @GlobalTheory.Proof.cm_localDensities_productFormula.densityProduct | exact GlobalTheory.Proof.cm_localDensities_productFormula.densityProduct | (intros; apply GlobalTheory.Proof.cm_localDensities_productFormula.densityProduct <;> assumption)
