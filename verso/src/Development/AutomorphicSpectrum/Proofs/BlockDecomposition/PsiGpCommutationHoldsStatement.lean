import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiGpCommutationHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPsiGpCommutationHolds.lean&line=385#L385)
-/
theorem _root_.GlobalTheory.T.psi_gp_commutation_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PsiGP k := by
  first | exact @GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP | exact GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP | (intros; apply GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP <;> assumption)
