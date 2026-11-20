import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharacterFockColumnSubstitutionEqZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
open Classical MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIntegralDetCharacterFockColumnSubstitutionEqZero.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.integral_detCharacter_fockColumnSubstitution_eq_zero : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ) (τ₀ : ι), 0 < a → 0 < m τ₀ → ∀ {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) →
    Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) ∂ν = 0 := by
  first | exact @GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero | exact GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero | (intros; apply GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero <;> assumption)
