import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfTwist
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf | exact GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf | (intros; apply GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.finite_support_of_twist : PositivityTheory.Rg.BcB.G8.Fin.SuppFinOf := by
  first | exact @GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf | exact GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf | (intros; apply GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf <;> assumption)
