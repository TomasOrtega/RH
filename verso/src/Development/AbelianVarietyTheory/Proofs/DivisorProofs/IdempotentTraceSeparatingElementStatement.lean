import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTraceSeparatingElement
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InvDifferentArith.indicator_inverseDifferent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIdempotentTraceSeparatingElement.lean&line=184#L184)
-/
theorem _root_.GlobalTheory.T.idempotent_trace_separating_element : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (C : Type) [Field C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∃ δ : C, δ ≠ 0 ∧ ∀ φ : E →+* C, (∃ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E), ∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then δ else 0) ∧ ∀ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E) (s : C), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then s else 0) → v s ≤ v δ := by
  first | exact @GlobalTheory.InvDifferentArith.indicator_inverseDifferent | exact GlobalTheory.InvDifferentArith.indicator_inverseDifferent | (intros; apply GlobalTheory.InvDifferentArith.indicator_inverseDifferent <;> assumption)
