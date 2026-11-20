import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProdEquivStandardBlocks
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMultiProdEquivStandardBlocks.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.multiProd_equiv_standard_blocks : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (e : (Σ a, Fin (d a)) ≃ Fin N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), Nonempty ((multiProd e π).Equiv (multiProd (stdBlocks d hd) π)) := by
  first | exact @GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks | exact GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks | (intros; apply GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks <;> assumption)
