import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoBasesComparison
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.LinAlg.twoBases | exact GlobalTheory.CompanionTheory.LinAlg.twoBases | (intros; apply GlobalTheory.CompanionTheory.LinAlg.twoBases <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.two_bases_comparison : TwoBases := by
  first | exact @GlobalTheory.CompanionTheory.LinAlg.twoBases | exact GlobalTheory.CompanionTheory.LinAlg.twoBases | (intros; apply GlobalTheory.CompanionTheory.LinAlg.twoBases <;> assumption)
