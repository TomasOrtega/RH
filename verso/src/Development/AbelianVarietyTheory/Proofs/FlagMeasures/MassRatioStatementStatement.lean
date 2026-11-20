import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioStatement
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MassAtRecord.massRatio_at_record` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMassRatioStatement.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.mass_ratio_statement : ∀ D : D7, UnitaryVolumeMass.stMassRatio D := by
  first | exact @GlobalTheory.MassAtRecord.massRatio_at_record | exact GlobalTheory.MassAtRecord.massRatio_at_record | (intros; apply GlobalTheory.MassAtRecord.massRatio_at_record <;> assumption)
