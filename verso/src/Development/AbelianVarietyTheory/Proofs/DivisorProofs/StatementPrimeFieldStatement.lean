import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StatementPrimeField
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.DegChTwo.statementPrimeField | exact GlobalTheory.DegChTwo.statementPrimeField | (intros; apply GlobalTheory.DegChTwo.statementPrimeField <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.statement_prime_field : GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.StatementPrimeField := by
  first | exact @GlobalTheory.DegChTwo.statementPrimeField | exact GlobalTheory.DegChTwo.statementPrimeField | (intros; apply GlobalTheory.DegChTwo.statementPrimeField <;> assumption)
