import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUniformiserAbovePrime
import Mathlib
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_global_uniformiser_above_prime` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsGlobalUniformiserAbovePrime.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_global_uniformizer_above_prime : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F], ∃ ϖ z : 𝓞 F, ϖ * z - (p : 𝓞 F) ∈ Ideal.span {(p : 𝓞 F) ^ 2} ∧ (∃ n : ℕ, ϖ ^ n ∈ Ideal.span {(p : 𝓞 F)}) ∧ IsReduced (𝓞 F ⧸ Ideal.span {(p : 𝓞 F), ϖ}) := by
  first | exact @GlobalTheory.exists_global_uniformiser_above_prime | exact GlobalTheory.exists_global_uniformiser_above_prime | (intros; apply GlobalTheory.exists_global_uniformiser_above_prime <;> assumption)
