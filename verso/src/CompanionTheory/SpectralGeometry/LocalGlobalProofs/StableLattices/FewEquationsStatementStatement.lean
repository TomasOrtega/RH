import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FewEquationsStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FewEq.fewEq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFewEquationsStatement.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.FewEquationsStatement : FewEqSt := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.fewEq | exact GlobalTheory.CompanionTheory.FewEq.fewEq | (intros; apply GlobalTheory.CompanionTheory.FewEq.fewEq <;> assumption)
