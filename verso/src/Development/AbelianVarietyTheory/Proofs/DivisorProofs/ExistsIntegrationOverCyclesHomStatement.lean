import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegrationOverCyclesHom
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
open GlobalTheory.AnPer
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIntegrationOverCyclesHom.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.exists_integrationOverCyclesHom : PHom := by
  first | exact @GlobalTheory.AnPer.pHom | exact GlobalTheory.AnPer.pHom | (intros; apply GlobalTheory.AnPer.pHom <;> assumption)
