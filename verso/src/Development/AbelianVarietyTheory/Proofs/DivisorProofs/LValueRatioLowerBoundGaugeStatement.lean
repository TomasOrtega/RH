import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LValueRatioLowerBoundGauge
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.lValueRatio_lower_bound_gauge : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → FieldDat → TorEx → RhoLow := by
  first | exact @GlobalTheory.RhoLowProof.rhoLow_holds | exact GlobalTheory.RhoLowProof.rhoLow_holds | (intros; apply GlobalTheory.RhoLowProof.rhoLow_holds <;> assumption)
