import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticRingOfIntegersMulMemSpanOneGen
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FQuadraticRingOfIntegersMulMemSpanOneGen.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.exists_denom_mul_mem_span_one_gen_of_finrank_two : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∃ (θ : 𝓞 E) (D : 𝓞 F), D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  first | exact @GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen | exact GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen | (intros; apply GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen <;> assumption)
