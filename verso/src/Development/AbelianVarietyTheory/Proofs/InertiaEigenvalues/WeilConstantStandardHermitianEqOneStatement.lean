import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConstantStandardHermitianEqOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.gammaOne_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWeilConstantStandardHermitianEqOne.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.weilConstantStandardHermitian_eq_one : GammaOne := by
  first | exact @GlobalTheory.JR.gammaOne_holds | exact GlobalTheory.JR.gammaOne_holds | (intros; apply GlobalTheory.JR.gammaOne_holds <;> assumption)
