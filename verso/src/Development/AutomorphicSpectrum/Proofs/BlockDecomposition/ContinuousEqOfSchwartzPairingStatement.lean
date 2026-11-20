import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousEqOfSchwartzPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FContinuousEqOfSchwartzPairing.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.continuous_eq_of_schwartz_pairing : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] (P Q : K → ℂ), Continuous P → Continuous Q → (∀ Φ ∈ SBE K, ∫ z, Φ z * P z ∂μ = ∫ z, Φ z * Q z ∂μ) → P = Q := by
  first | exact @GlobalTheory.CompanionTheory.SBSep.eq_of_integral_SBE_eq | exact GlobalTheory.CompanionTheory.SBSep.eq_of_integral_SBE_eq | (intros; apply GlobalTheory.CompanionTheory.SBSep.eq_of_integral_SBE_eq <;> assumption)
