import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftSideFormula
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.SW.LS.lside | exact GlobalTheory.CompanionTheory.SW.LS.lside | (intros; apply GlobalTheory.CompanionTheory.SW.LS.lside <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.left_side_formula : Equi → CoCpt → LSide := by
  first | exact @GlobalTheory.CompanionTheory.SW.LS.lside | exact GlobalTheory.CompanionTheory.SW.LS.lside | (intros; apply GlobalTheory.CompanionTheory.SW.LS.lside <;> assumption)
