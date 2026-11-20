import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ArithmeticRelationsStatementHolds
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.RelationsStatement
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FArithmeticRelationsStatementHolds.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.arithmetic_relations_statement_holds : GlobalTheory.CompanionTheory.Ar.Num.RelationsStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.TopRel.relations | exact GlobalTheory.CompanionTheory.Ar.Num.TopRel.relations | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.TopRel.relations <;> assumption)
