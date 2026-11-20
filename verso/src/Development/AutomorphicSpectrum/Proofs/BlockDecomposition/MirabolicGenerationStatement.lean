import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicGeneration
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMirabolicGeneration.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.mirabolic_generation : SecLaw → TestSph → AvgMem → AvgInv → SideOf → TestK → Core → MirGen := by
  first | exact @GlobalTheory.CompanionTheory.EisMir.mirGen_of_core | exact GlobalTheory.CompanionTheory.EisMir.mirGen_of_core | (intros; apply GlobalTheory.CompanionTheory.EisMir.mirGen_of_core <;> assumption)
