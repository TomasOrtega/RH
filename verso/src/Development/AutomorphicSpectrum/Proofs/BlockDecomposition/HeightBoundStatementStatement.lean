import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.height_bound_statement : GlobalTheory.CompanionTheory.Jp.JpHgt := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Hgt.jpHgt | exact GlobalTheory.CompanionTheory.Jp.Hgt.jpHgt | (intros; apply GlobalTheory.CompanionTheory.Jp.Hgt.jpHgt <;> assumption)
