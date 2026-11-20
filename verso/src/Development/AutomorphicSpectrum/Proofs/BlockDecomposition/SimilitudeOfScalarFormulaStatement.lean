import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeOfScalarFormula
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.SW.BaseSimil.simil | exact GlobalTheory.CompanionTheory.SW.BaseSimil.simil | (intros; apply GlobalTheory.CompanionTheory.SW.BaseSimil.simil <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.similitude_of_scalar_formula : Scal → Simil := by
  first | exact @GlobalTheory.CompanionTheory.SW.BaseSimil.simil | exact GlobalTheory.CompanionTheory.SW.BaseSimil.simil | (intros; apply GlobalTheory.CompanionTheory.SW.BaseSimil.simil <;> assumption)
