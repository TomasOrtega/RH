import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiscreteSpectrum
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.FinCut

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FinDiscN.finDiscN` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteDiscreteSpectrum.lean&line=383#L383)
-/
theorem _root_.GlobalTheory.T.finite_discrete_spectrum : PositivityTheory.Rg.BcB.F.F5.FinDiscN := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscN.finDiscN | exact GlobalTheory.CompanionTheory.FinDiscN.finDiscN | (intros; apply GlobalTheory.CompanionTheory.FinDiscN.finDiscN <;> assumption)
