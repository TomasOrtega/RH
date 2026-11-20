import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitCoeffGaloisLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Sieg.sg_coeff_galois_int` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSmoothedSiegelUnitCoeffGaloisLevel.lean&line=304#L304)
-/
theorem _root_.GlobalTheory.T.smoothedSiegelUnit_coeff_galois_level : ∀ (c M a b d : ℕ) (σ : ℂ ≃+* ℂ), 0 < M → a < M → σ (ee (1 / (M : ℂ))) = ee ((d : ℂ) / M) → admitted c ![(a : ℚ) / M, (b : ℚ) / M] → admitted c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] → ∃ (k : ℤ) (A : ℕ → ℂ), HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) A ∧ HasQ M (fun τ => sg c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => σ (A n)) := by
  first | exact @GlobalTheory.Sieg.sg_coeff_galois_int | exact GlobalTheory.Sieg.sg_coeff_galois_int | (intros; apply GlobalTheory.Sieg.sg_coeff_galois_int <;> assumption)
