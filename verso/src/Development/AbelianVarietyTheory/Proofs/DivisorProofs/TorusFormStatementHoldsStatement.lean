import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFormStatementHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorusFormPf.torusForm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorusFormStatementHolds.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.torus_form_statement_holds : TorusForm := by
  first | exact @GlobalTheory.TorusFormPf.torusForm | exact GlobalTheory.TorusFormPf.torusForm | (intros; apply GlobalTheory.TorusFormPf.torusForm <;> assumption)
