import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedSpaceDualVectorTraceForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.dualform` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsMixedSpaceDualVectorTraceForm.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_mixedSpace_dual_vector_traceForm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z : mixedEmbedding.mixedSpace F, z ≠ 0 → ∃ u, ℓ (z * u) ≠ 0) →
    ∀ lam : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ, ∃ u : κ → mixedEmbedding.mixedSpace F,
      ∀ x, ℓ (∑ k, x k * u k) = lam x := by
  first | exact @GlobalTheory.dualform | exact GlobalTheory.dualform | (intros; apply GlobalTheory.dualform <;> assumption)
