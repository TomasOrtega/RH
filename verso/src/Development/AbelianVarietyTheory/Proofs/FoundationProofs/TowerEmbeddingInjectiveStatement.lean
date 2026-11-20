import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerEmbeddingInjective
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FTowerEmbeddingInjective.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.tower_embedding_injective : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι → Function.Injective ι := by
  first | exact @GlobalTheory.K5.EmbInj.emb_injective | exact GlobalTheory.K5.EmbInj.emb_injective | (intros; apply GlobalTheory.K5.EmbInj.emb_injective <;> assumption)
