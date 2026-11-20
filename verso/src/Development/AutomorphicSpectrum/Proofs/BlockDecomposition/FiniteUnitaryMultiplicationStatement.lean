import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteUnitaryMultiplication
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.FUMulPf.fuMul | exact GlobalTheory.CompanionTheory.FUMulPf.fuMul | (intros; apply GlobalTheory.CompanionTheory.FUMulPf.fuMul <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.finite_unitary_multiplication : FUMul := by
  first | exact @GlobalTheory.CompanionTheory.FUMulPf.fuMul | exact GlobalTheory.CompanionTheory.FUMulPf.fuMul | (intros; apply GlobalTheory.CompanionTheory.FUMulPf.fuMul <;> assumption)
