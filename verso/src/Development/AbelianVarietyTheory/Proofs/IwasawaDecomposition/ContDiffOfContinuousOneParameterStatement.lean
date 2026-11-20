import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter
open MeasureTheory Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.contDiff_of_continuous_oneParameter` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FContDiffOfContinuousOneParameter.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.contDiff_of_continuous_oneParameter_hom : ∀ (A : Type) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] (T : ℝ → A), Continuous T → T 0 = 1 → (∀ s t, T (s + t) = T s * T t) → ContDiff ℝ ∞ T := by
  first | exact @GlobalTheory.contDiff_of_continuous_oneParameter | exact GlobalTheory.contDiff_of_continuous_oneParameter | (intros; apply GlobalTheory.contDiff_of_continuous_oneParameter <;> assumption)
