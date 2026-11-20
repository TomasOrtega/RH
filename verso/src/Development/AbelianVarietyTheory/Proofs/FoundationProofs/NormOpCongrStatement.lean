import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpCongr
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FNormOpCongr.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.normOp_congr_mod_pow_succ : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ (h₁ h₂ r : PowerSeries R) (k : ℕ), 1 ≤ k → IsUnit h₂ → h₁ = h₂ + (p : PowerSeries R) ^ k * r → ∃ r' : PowerSeries R, normOp p h₁ = normOp p h₂ + (p : PowerSeries R) ^ (k + 1) * r' := by
  first | exact @GlobalTheory.Col.normOp_congr | exact GlobalTheory.Col.normOp_congr | (intros; apply GlobalTheory.Col.normOp_congr <;> assumption)
