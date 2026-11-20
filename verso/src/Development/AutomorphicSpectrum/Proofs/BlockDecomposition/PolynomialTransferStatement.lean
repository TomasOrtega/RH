import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialTransfer
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPolynomialTransfer.lean&line=140#L140)
-/
theorem _root_.GlobalTheory.T.polynomial_transfer : KH.PolyTf := by
  first | exact @GlobalTheory.CompanionTheory.PolyTfCon.polyTf | exact GlobalTheory.CompanionTheory.PolyTfCon.polyTf | (intros; apply GlobalTheory.CompanionTheory.PolyTfCon.polyTf <;> assumption)
