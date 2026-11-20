import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegree
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FProjectionFormulaDegree.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.projection_formula_degree : GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree | exact GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree | (intros; apply GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree <;> assumption)
