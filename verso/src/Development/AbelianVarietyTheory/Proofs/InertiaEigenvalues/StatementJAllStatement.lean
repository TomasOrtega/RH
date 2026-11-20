import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StatementJAll
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JumpStatement.holds_all` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FStatementJAll.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.statement_J_all : ∀ D : D7, AdmissibleParameterJ.JumpBoundClosedForm D := by
  first | exact @GlobalTheory.JumpStatement.holds_all | exact GlobalTheory.JumpStatement.holds_all | (intros; apply GlobalTheory.JumpStatement.holds_all <;> assumption)
