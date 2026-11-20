import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundednessStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.uniform_boundedness_statement : GlobalTheory.CompanionTheory.Jp.JpUnif := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Unif.jpUnif | exact GlobalTheory.CompanionTheory.Jp.Unif.jpUnif | (intros; apply GlobalTheory.CompanionTheory.Jp.Unif.jpUnif <;> assumption)
