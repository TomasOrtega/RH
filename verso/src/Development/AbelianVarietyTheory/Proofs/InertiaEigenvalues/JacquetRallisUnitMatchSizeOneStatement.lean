import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSizeOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.JR.SizeOne.unitMatch_zero | exact GlobalTheory.JR.SizeOne.unitMatch_zero | (intros; apply GlobalTheory.JR.SizeOne.unitMatch_zero <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_sizeOne : UnitMatch 0 := by
  first | exact @GlobalTheory.JR.SizeOne.unitMatch_zero | exact GlobalTheory.JR.SizeOne.unitMatch_zero | (intros; apply GlobalTheory.JR.SizeOne.unitMatch_zero <;> assumption)
