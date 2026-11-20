import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryIwasawaIntegrationFormulaRealPlace
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagMeas.iwasawaFormula` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FUnitaryIwasawaIntegrationFormulaRealPlace.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.unitary_iwasawa_integration_formula_real_place : IwasawaFormula := by
  first | exact @GlobalTheory.FlagMeas.iwasawaFormula | exact GlobalTheory.FlagMeas.iwasawaFormula | (intros; apply GlobalTheory.FlagMeas.iwasawaFormula <;> assumption)
