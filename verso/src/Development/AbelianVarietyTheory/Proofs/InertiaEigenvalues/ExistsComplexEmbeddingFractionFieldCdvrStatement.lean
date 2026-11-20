import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvr
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsComplexEmbeddingFractionFieldCdvr.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.exists_complex_embedding_fractionField_cdvr : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T : CDVR), T.FinRes → ∀ io : K →+* T.Fr, ∃ ι : T.Fr →+* ℂ, ι.comp io = σ := by
  first | exact @GlobalTheory.ComplexEmbedding.exists_embedding_fractionField | exact GlobalTheory.ComplexEmbedding.exists_embedding_fractionField | (intros; apply GlobalTheory.ComplexEmbedding.exists_embedding_fractionField <;> assumption)
