import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFive
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnramifiedQuadraticConditionFive.lean&line=349#L349)
-/
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_five : PositivityTheory.SiegelWeilFormula.Gunr.Q5 := by
  first | exact @GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot | exact GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot | (intros; apply GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot <;> assumption)
