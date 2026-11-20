import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormula
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgMass.cnt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCountingFormula.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.counting_formula : TestEx → LSide → RSide → Cnt := by
  first | exact @GlobalTheory.CompanionTheory.RgMass.cnt | exact GlobalTheory.CompanionTheory.RgMass.cnt | (intros; apply GlobalTheory.CompanionTheory.RgMass.cnt <;> assumption)
