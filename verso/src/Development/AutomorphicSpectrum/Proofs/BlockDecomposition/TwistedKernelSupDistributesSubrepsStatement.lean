import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelSupDistributesSubreps
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PRep.WhitSup.sup_inf_twKer_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTwistedKernelSupDistributesSubreps.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.twisted_kernel_sup_distributes_subreps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → ∀ X Y : Subrepresentation ρ, (X ⊔ Y).toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ≤ X.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ⊔ Y.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.PRep.WhitSup.sup_inf_twKer_le | exact GlobalTheory.CompanionTheory.PRep.WhitSup.sup_inf_twKer_le | (intros; apply GlobalTheory.CompanionTheory.PRep.WhitSup.sup_inf_twKer_le <;> assumption)
