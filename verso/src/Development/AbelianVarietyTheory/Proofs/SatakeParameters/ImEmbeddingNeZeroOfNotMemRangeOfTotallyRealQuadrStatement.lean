import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImEmbeddingNeZeroOfNotMemRangeOfTotallyRealQuadr
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FImEmbeddingNeZeroOfNotMemRangeOfTotallyRealQuadr.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.im_embedding_ne_zero_of_not_mem_range_algebraMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (w : InfinitePlace E) (θ : E), θ ∉ Set.range (algebraMap F E) → (w.embedding θ).im ≠ 0 := by
  first | exact @GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic | exact GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic | (intros; apply GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic <;> assumption)
