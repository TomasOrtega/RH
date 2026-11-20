import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsZeroTranslationInvariantOfLocallyConst
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isTest_nhds_inv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsNhdsZeroTranslationInvariantOfLocallyConst.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (f : X → ℂ), IsTest f → ∃ U ∈ 𝓝 (0 : X), ∀ x : X, ∀ u ∈ U, f (x + u) = f x := by
  first | exact @GlobalTheory.isTest_nhds_inv | exact GlobalTheory.isTest_nhds_inv | (intros; apply GlobalTheory.isTest_nhds_inv <;> assumption)
