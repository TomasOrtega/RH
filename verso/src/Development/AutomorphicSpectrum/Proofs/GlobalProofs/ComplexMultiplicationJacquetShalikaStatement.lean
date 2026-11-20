import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ComplexMultiplicationJacquetShalika
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Published.complexMultiplicationJ | exact GlobalTheory.CompanionTheory.Published.complexMultiplicationJ | (intros; apply GlobalTheory.CompanionTheory.Published.complexMultiplicationJ <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.complex_multiplication_jacquet_shalika : GlobalTheory.Published.ComplexMultiplicationJSt := by
  first | exact @GlobalTheory.CompanionTheory.Published.complexMultiplicationJ | exact GlobalTheory.CompanionTheory.Published.complexMultiplicationJ | (intros; apply GlobalTheory.CompanionTheory.Published.complexMultiplicationJ <;> assumption)
