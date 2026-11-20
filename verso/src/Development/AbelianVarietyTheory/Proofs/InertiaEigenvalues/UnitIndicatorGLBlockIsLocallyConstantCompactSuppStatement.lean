import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockIsLocallyConstantCompactSupp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnitIndicatorGLBlockIsLocallyConstantCompactSupp.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.unitIndicatorGLBlock_isLocallyConstantCompactSupport : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (r : ℕ), IsTest (unitG r F) := by
  first | exact @GlobalTheory.JR.UnitTest.unitG_isTest | exact GlobalTheory.JR.UnitTest.unitG_isTest | (intros; apply GlobalTheory.JR.UnitTest.unitG_isTest <;> assumption)
