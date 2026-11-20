import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedVanishing
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LocGrStep.loc_gr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalGradedVanishing.lean&line=510#L510)
-/
theorem _root_.GlobalTheory.T.local_graded_vanishing : KH.LocGr := by
  first | exact @GlobalTheory.CompanionTheory.LocGrStep.loc_gr | exact GlobalTheory.CompanionTheory.LocGrStep.loc_gr | (intros; apply GlobalTheory.CompanionTheory.LocGrStep.loc_gr <;> assumption)
