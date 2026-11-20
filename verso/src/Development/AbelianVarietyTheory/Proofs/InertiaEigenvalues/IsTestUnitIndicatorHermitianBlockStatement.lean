import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTestUnitIndicatorHermitianBlock
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsTestUnitIndicatorHermitianBlock.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.isTest_unitIndicatorHermitianBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E] [IsUltrametricDist F] [LocallyCompactSpace F] [IsUltrametricDist E] [LocallyCompactSpace E] (r : ℕ), (∀ y : E, ‖star y‖ = ‖y‖) → IsTest (unitU r F E) := by
  first | exact @GlobalTheory.JR.isTest_unitU | exact GlobalTheory.JR.isTest_unitU | (intros; apply GlobalTheory.JR.isTest_unitU <;> assumption)
