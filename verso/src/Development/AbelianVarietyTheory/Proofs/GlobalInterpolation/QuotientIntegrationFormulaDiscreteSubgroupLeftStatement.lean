import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.QuotDiscrete.discreteClause | exact GlobalTheory.QuotDiscrete.discreteClause | (intros; apply GlobalTheory.QuotDiscrete.discreteClause <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.quotient_integration_formula_discrete_subgroup_left : DiscreteClause := by
  first | exact @GlobalTheory.QuotDiscrete.discreteClause | exact GlobalTheory.QuotDiscrete.discreteClause | (intros; apply GlobalTheory.QuotDiscrete.discreteClause <;> assumption)
