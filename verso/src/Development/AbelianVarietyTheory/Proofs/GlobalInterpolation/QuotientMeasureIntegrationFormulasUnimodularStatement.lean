import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientMeasureIntegrationFormulasUnimodular
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures | exact GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures | (intros; apply GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quoti …`.
-/
theorem _root_.GlobalTheory.T.quotientMeasure_integration_formulas_unimodular : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures := by
  first | exact @GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures | exact GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures | (intros; apply GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures <;> assumption)
