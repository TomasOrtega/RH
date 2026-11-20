import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityInert
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.MuInertPlace.muInert` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMultiplicityInert.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.multiplicity_inert : PositivityTheory.Rg.BcB.F.MLM.MuInert := by
  first | exact @GlobalTheory.CompanionTheory.MuInertPlace.muInert | exact GlobalTheory.CompanionTheory.MuInertPlace.muInert | (intros; apply GlobalTheory.CompanionTheory.MuInertPlace.muInert <;> assumption)
