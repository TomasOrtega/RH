import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionSphericalK
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTestFunctionSphericalK.lean&line=94#L94)
-/
theorem _root_.GlobalTheory.T.test_function_spherical_K : StdGood → BdetLaw → TestFun → TestK := by
  first | exact @GlobalTheory.CompanionTheory.EisTestK.testK | exact GlobalTheory.CompanionTheory.EisTestK.testK | (intros; apply GlobalTheory.CompanionTheory.EisTestK.testK <;> assumption)
