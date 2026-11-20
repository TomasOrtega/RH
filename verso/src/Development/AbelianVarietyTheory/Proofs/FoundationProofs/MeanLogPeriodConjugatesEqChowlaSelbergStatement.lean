import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanLogPeriodConjugatesEqChowlaSelberg
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PeriodMean.mean_log_period` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMeanLogPeriodConjugatesEqChowlaSelberg.lean&line=202#L202)
-/
theorem _root_.GlobalTheory.T.mean_log_period_conjugates_eq_chowlaSelberg : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)) / Real.pi)) / (Module.finrank ℚ M : ℝ) = Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt D.host.d) - logDerivativeAtOne D := by
  first | exact @GlobalTheory.PeriodMean.mean_log_period | exact GlobalTheory.PeriodMean.mean_log_period | (intros; apply GlobalTheory.PeriodMean.mean_log_period <;> assumption)
