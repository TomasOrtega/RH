import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralGLZeroOfRadicalIntegrals
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
open MeasureTheory GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FWeightedOrbitalIntegralGLZeroOfRadicalIntegrals.lean&line=359#L359)
-/
theorem _root_.GlobalTheory.T.weightedOrbitalIntegral_GL_zero_of_radical_integrals : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ) [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k)) [μ.IsHaarMeasure] (ε : Matrix (Fin r) (Fin r) k) (N : Subgroup (GL (Fin r) k)), ε * ε = ε → (∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) → ∀ f : GL (Fin r) k → ℂ, Continuous f → HasCompactSupport f → (∀ (ν : Measure N) [ν.IsHaarMeasure] (x y : GL (Fin r) k), ∫ u : N, f (x * u * y) ∂ν = 0) → ∀ γ : GL (Fin r) k, IsRegSS γ.1 → γ.1 * ε = ε * γ.1 → ∀ b : GL (Fin r) k → ℂ, Continuous b → LeftInv (cent γ) b → LeftInv N b → ∀ (dt : Measure (cent γ)) [dt.IsHaarMeasure], HasQuotInt (cent γ) dt μ (fun x => b x * f (x⁻¹ * γ * x)) 0 := by
  first | exact @GlobalTheory.RadicalOrb.hasQuotInt_zero | exact GlobalTheory.RadicalOrb.hasQuotInt_zero | (intros; apply GlobalTheory.RadicalOrb.hasQuotInt_zero <;> assumption)
