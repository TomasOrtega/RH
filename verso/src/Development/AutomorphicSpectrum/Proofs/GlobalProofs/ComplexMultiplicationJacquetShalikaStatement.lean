import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ComplexMultiplicationJacquetShalika
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Published.complexMultiplicationJ` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FComplexMultiplicationJacquetShalika.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.complex_multiplication_jacquet_shalika : GlobalTheory.Published.ComplexMultiplicationJSt := by
  first | exact @GlobalTheory.CompanionTheory.Published.complexMultiplicationJ | exact GlobalTheory.CompanionTheory.Published.complexMultiplicationJ | (intros; apply GlobalTheory.CompanionTheory.Published.complexMultiplicationJ <;> assumption)
