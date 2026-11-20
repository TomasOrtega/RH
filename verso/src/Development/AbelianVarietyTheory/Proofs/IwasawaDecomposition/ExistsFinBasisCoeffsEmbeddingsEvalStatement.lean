import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinBasisCoeffsEmbeddingsEval
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsFinBasisCoeffsEmbeddingsEval.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_finBasis_coeffs_embeddings_eval : ∀ (L : Type) [Field L] [NumberField L] (K : Type) [Field K] [CharZero K] (z : (L →+* K) → K), ∃ y : Fin (Module.finrank ℚ L) → K, ∀ σ : L →+* K, ∑ i, σ (Module.finBasis ℚ L i) * y i = z σ := by
  first | exact @GlobalTheory.embeddings_eval_onto | exact GlobalTheory.embeddings_eval_onto | (intros; apply GlobalTheory.embeddings_eval_onto <;> assumption)
