import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagFurtherTermIndependentStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisFurther
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FFlagFurtherTermIndependentStatement.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.flag_further_term_independent_statement : GroundTheory.Heights₂.Heights.NumbersDVR.flagFurtherTerm_independent.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.flag_further_term_independent | exact GlobalTheory.CompanionTheory.Ar.Num.flag_further_term_independent | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.flag_further_term_independent <;> assumption)
