import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeIntegratedOperatorRangesPolynomial
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.shapeIntegratedOperator_ranges_polynomial : GlobalTheory.PsCo.Pc3.RangeShape := by
  first | exact @GlobalTheory.PsCo.Pc3.rangeShape | exact GlobalTheory.PsCo.Pc3.rangeShape | (intros; apply GlobalTheory.PsCo.Pc3.rangeShape <;> assumption)
