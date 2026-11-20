import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalAlgebraHolds.lean&line=317#L317)
-/
theorem _root_.GlobalTheory.T.local_algebra_holds : LocAlg := by
  first | exact @GlobalTheory.CompanionTheory.LocHecke.locAlg | exact GlobalTheory.CompanionTheory.LocHecke.locAlg | (intros; apply GlobalTheory.CompanionTheory.LocHecke.locAlg <;> assumption)
