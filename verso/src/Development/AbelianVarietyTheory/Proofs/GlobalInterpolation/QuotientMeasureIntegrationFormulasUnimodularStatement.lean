import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientMeasureIntegrationFormulasUnimodular
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FQuotientMeasureIntegrationFormulasUnimodular.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.quotientMeasure_integration_formulas_unimodular : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures := by
  first | exact @GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures | exact GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures | (intros; apply GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures <;> assumption)
