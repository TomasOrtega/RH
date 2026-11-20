import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MkFiber
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PExpbSt
open PositivityTheory.Rg.BcB.F.Tail.BS
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.IwJac.jacHk | exact GlobalTheory.CompanionTheory.IwJac.jacHk | (intros; apply GlobalTheory.CompanionTheory.IwJac.jacHk <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.jacquet_hecke_jacHk : JacHk := by
  first | exact @GlobalTheory.CompanionTheory.IwJac.jacHk | exact GlobalTheory.CompanionTheory.IwJac.jacHk | (intros; apply GlobalTheory.CompanionTheory.IwJac.jacHk <;> assumption)
