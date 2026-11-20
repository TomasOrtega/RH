import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionProductRankZeroRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRestrictionProductRankZeroRight.lean&line=161#L161)
-/
theorem _root_.GlobalTheory.T.restriction_product_rank_zero_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i n : ℕ) (π₁ : GRep k (i + 1)) (π₂ : GRep k 0) (h : (i + 1) + 0 = n + 1) (h' : i + 0 = n), IsSmooth π₁.ρ → IsSmooth π₂.ρ → MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodPGn (gres π₁) π₂)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibTrivBlock.miso_gres_prod_zero | exact GlobalTheory.CompanionTheory.LeibTrivBlock.miso_gres_prod_zero | (intros; apply GlobalTheory.CompanionTheory.LeibTrivBlock.miso_gres_prod_zero <;> assumption)
