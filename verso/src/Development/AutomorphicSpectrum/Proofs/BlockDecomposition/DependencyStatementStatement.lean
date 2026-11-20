import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DependencyStatement
import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FewEq.depSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDependencyStatement.lean&line=148#L148)
-/
theorem _root_.GlobalTheory.T.dependency_statement : DepSt := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.depSt | exact GlobalTheory.CompanionTheory.FewEq.depSt | (intros; apply GlobalTheory.CompanionTheory.FewEq.depSt <;> assumption)
