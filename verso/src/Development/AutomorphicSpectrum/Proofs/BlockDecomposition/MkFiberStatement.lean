import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MkFiber
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PExpbSt
open PositivityTheory.Rg.BcB.F.Tail.BS
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.IwJac.jacHk` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMkFiber.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.jacquet_hecke_jacHk : JacHk := by
  first | exact @GlobalTheory.CompanionTheory.IwJac.jacHk | exact GlobalTheory.CompanionTheory.IwJac.jacHk | (intros; apply GlobalTheory.CompanionTheory.IwJac.jacHk <;> assumption)
