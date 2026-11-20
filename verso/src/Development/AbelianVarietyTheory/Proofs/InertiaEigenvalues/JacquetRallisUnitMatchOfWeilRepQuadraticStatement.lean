import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchOfWeilRepQuadratic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FJacquetRallisUnitMatchOfWeilRepQuadratic.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_of_weilRep_quadratic : WeilField → ∀ r, UnitMatch r := by
  first | exact @GlobalTheory.JR.unitMatch_of_weilField | exact GlobalTheory.JR.unitMatch_of_weilField | (intros; apply GlobalTheory.JR.unitMatch_of_weilField <;> assumption)
