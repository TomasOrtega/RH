import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleContragredientOfInducedProduct
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ContraProd.contra_contra_prodIrr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDoubleContragredientOfInducedProduct.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.double_contragredient_of_induced_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), Nonempty ((contra (contra (prodIrr x hd))).Equiv (prodIrr x hd)) := by
  first | exact @GlobalTheory.CompanionTheory.ContraProd.contra_contra_prodIrr | exact GlobalTheory.CompanionTheory.ContraProd.contra_contra_prodIrr | (intros; apply GlobalTheory.CompanionTheory.ContraProd.contra_contra_prodIrr <;> assumption)
