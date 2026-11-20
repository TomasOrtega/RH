import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelAdjointRegular
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WaveMult.adjoint_kernel_reg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FKernelAdjointRegular.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.kernel_adjoint_regular : LgFacts → ∀ (n : ℕ) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)), KReg k → (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) → (haveI := FiniteDimensional.complete ℂ E.V; KReg (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) ∧ ∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, ContinuousLinearMap.adjoint (k (k₁.1 * y * k₂.1)⁻¹) = E.ρ k₁ * ContinuousLinearMap.adjoint (k y⁻¹) * E.ρ k₂) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.adjoint_kernel_reg | exact GlobalTheory.CompanionTheory.WaveMult.adjoint_kernel_reg | (intros; apply GlobalTheory.CompanionTheory.WaveMult.adjoint_kernel_reg <;> assumption)
