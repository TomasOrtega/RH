import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionSideEquidistribution
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.l_function_side_equidistribution : PositivityTheory.Rg.Mass.Equi → LSide := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside <;> assumption)
