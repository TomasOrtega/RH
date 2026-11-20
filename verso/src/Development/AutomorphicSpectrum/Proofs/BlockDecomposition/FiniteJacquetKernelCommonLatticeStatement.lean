import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteJacquetKernelCommonLattice
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZPsiPG.FibKer.exists_Lc_finite_twKer` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteJacquetKernelCommonLattice.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.finite_jacquet_kernel_common_lattice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (S : Set X), S.Finite → (∀ x ∈ S, x ∈ twKer ρ ⊤ 1) → ∃ c : k, c ≠ 0 ∧ ∀ x ∈ S, x ∈ twKer ρ (Lc n c) 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.exists_Lc_finite_twKer | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.exists_Lc_finite_twKer | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.exists_Lc_finite_twKer <;> assumption)
