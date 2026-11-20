import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductRankLeOne
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTensorProductRankLeOne.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.tensor_product_rank_le_one : ∀ {α : Type} [Fintype α] (M : α → Type) [∀ a, AddCommGroup (M a)] [∀ a, Module ℂ (M a)], (∀ a, Module.rank ℂ (M a) ≤ 1) → Module.rank ℂ (⨂[ℂ] a, M a) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.TensorRank.rank_piTensorProduct_le_one | exact GlobalTheory.CompanionTheory.TensorRank.rank_piTensorProduct_le_one | (intros; apply GlobalTheory.CompanionTheory.TensorRank.rank_piTensorProduct_le_one <;> assumption)
