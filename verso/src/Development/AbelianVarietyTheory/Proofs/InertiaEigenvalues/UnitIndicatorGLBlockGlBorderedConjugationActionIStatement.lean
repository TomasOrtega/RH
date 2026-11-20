import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockGlBorderedConjugationActionI
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnitIndicatorGLBlockGlBorderedConjugationActionI.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.unitIndicatorGLBlock_glBorderedConjugationAction_integral : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F), k ∈ glO n F → ∀ Y : Gl n F, unitG n F (act k Y) = unitG n F Y := by
  first | exact @GlobalTheory.JR.GLift.unitG_act | exact GlobalTheory.JR.GLift.unitG_act | (intros; apply GlobalTheory.JR.GLift.unitG_act <;> assumption)
