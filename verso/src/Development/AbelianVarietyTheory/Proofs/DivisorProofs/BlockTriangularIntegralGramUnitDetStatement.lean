import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockTriangularIntegralGramUnitDet
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBlockTriangularIntegralGramUnitDet.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.block_triangular_integral_gram_unit_det : ∀ {K : Type} [Field K] (w : AbsoluteValue K ℝ) (O : ValuationSubring K), (∀ x, x ∈ O ↔ w x ≤ 1) →
    ∀ {N : ℕ} (G Ba Bb : Matrix (Fin N) (Fin N) K) (d ga gb : Fin N → K), Ba.BlockTriangular id → Bb.BlockTriangular id →
    (∀ i, w (Ba i i * ga i - d i) < w (d i)) → (∀ i, w (Bb i i * gb i - d i) < w (d i)) →
    (∀ i k, w ((G * Ba) i k) ≤ 1) → (∀ i k, w ((G * Bb) i k) ≤ 1) → w (G * Ba).det = 1 → w (G * Bb).det = 1 →
    ∀ i, (∀ k, k < i → ((G * Ba)⁻¹ * (G * Bb)) i k = 0) ∧ w (((G * Ba)⁻¹ * (G * Bb)) i i - ga i / gb i) < 1 := by
  first | exact @GlobalTheory.triangular_change_of_frames | exact GlobalTheory.triangular_change_of_frames | (intros; apply GlobalTheory.triangular_change_of_frames <;> assumption)
