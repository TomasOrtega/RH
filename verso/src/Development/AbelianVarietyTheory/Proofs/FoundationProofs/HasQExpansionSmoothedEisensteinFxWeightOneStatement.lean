import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSmoothedEisensteinFxWeightOne
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
import Development.AbelianVarietyTheory.Definitions.Foundations.CthFac
import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperations
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Sieg.EisQ.hasQ_cF_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHasQExpansionSmoothedEisensteinFxWeightOne.lean&line=192#L192)
-/
theorem _root_.GlobalTheory.T.hasQExpansion_smoothedEisensteinFx_weightOne : ∀ (c M : ℕ) (a b : ℤ), 0 < M → GlobalTheory.QFam.HasQ M (GlobalTheory.Sieg.cF c 1 ![(a : ℚ) / M, (b : ℚ) / M]) (GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M (GlobalTheory.Sieg.ee (1 / (M : ℂ))) a b) := by
  first | exact @GlobalTheory.Sieg.EisQ.hasQ_cF_one | exact GlobalTheory.Sieg.EisQ.hasQ_cF_one | (intros; apply GlobalTheory.Sieg.EisQ.hasQ_cF_one; all_goals assumption)
