import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeTheoremOfPerfect
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CubePerf.cubeTheorem_of_perfAll` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCubeTheoremOfPerfect.lean&line=167#L167)
-/
theorem _root_.GlobalTheory.T.cube_theorem_of_perfect : GlobalTheory.SpreadingModels.PerfAll → GlobalTheory.Published.CubeTheorem := by
  first | exact @GlobalTheory.CompanionTheory.CubePerf.cubeTheorem_of_perfAll | exact GlobalTheory.CompanionTheory.CubePerf.cubeTheorem_of_perfAll | (intros; apply GlobalTheory.CompanionTheory.CubePerf.cubeTheorem_of_perfAll <;> assumption)
