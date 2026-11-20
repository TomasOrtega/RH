import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenRightInvarianceLocalCoefficient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth.isOpen_eC_invariant` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIsOpenRightInvarianceLocalCoefficient.lean&line=93#L93)
-/
theorem _root_.GlobalTheory.T.isOpen_right_invariance_local_coefficient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ), IsOpen {g : Mir k ((i + 1) + t) | ∀ m, eC ψ f (m * g) = eC ψ f m} := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth.isOpen_eC_invariant | exact GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth.isOpen_eC_invariant | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth.isOpen_eC_invariant <;> assumption)
