import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LOneSatakeBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.OneSat.lOneSat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLOneSatakeBound.lean&line=156#L156)
-/
theorem _root_.GlobalTheory.T.l_one_satake_bound : PositivityTheory.SphericalProduct.LOneSat := by
  first | exact @GlobalTheory.CompanionTheory.OneSat.lOneSat | exact GlobalTheory.CompanionTheory.OneSat.lOneSat | (intros; apply GlobalTheory.CompanionTheory.OneSat.lOneSat <;> assumption)
