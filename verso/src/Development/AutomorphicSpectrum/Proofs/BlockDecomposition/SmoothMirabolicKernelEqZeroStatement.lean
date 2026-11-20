import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothMirabolicKernelEqZero
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSmoothMirabolicKernelEqZero.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.smooth_mirabolic_kernel_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (m + 1)) V), IsSmooth τ → ∀ v : V, v ∈ twKer τ (MirUin k (m + 1)) 1 → (∀ g : GL (Fin (m + 1)) k, τ (levi k (m + 1) g) v ∈ twKer τ (MirUin k (m + 1)) (mirChar k ψ m)) → v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.eq_zero_of_forall_twKer | exact GlobalTheory.CompanionTheory.MirFourier.eq_zero_of_forall_twKer | (intros; apply GlobalTheory.CompanionTheory.MirFourier.eq_zero_of_forall_twKer <;> assumption)
