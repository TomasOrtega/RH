import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankProductLeOne
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductRankLeOneStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerRankProductLeOne.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.whittaker_rank_product_le_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), Module.rank ℂ (TwJacquet (prodIrr x hd) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.RgGu.rank_twJacquet_prodIrr_le_one | exact GlobalTheory.CompanionTheory.RgGu.rank_twJacquet_prodIrr_le_one | (intros; apply GlobalTheory.CompanionTheory.RgGu.rank_twJacquet_prodIrr_le_one <;> assumption)
