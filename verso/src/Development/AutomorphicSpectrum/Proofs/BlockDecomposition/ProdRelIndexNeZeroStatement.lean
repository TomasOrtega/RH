import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdRelIndexNeZero

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FProdRelIndexNeZero.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.prod_rel_index_ne_zero : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂), I₁.relIndex K₁ ≠ 0 → I₂.relIndex K₂ ≠ 0 → (I₁.prod I₂).relIndex (K₁.prod K₂) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero | exact GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero | (intros; apply GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero <;> assumption)
