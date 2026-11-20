import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionEquicontinuous
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariantTotallyComplexStatement
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FKernelEigenfunctionEquicontinuous.lean&line=170#L170)
-/
theorem _root_.GlobalTheory.T.kernel_eigenfunction_equicontinuous : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∀ η : ℝ≥0∞, 0 < η → ∃ U ∈ 𝓝 (1 : GA E N), ∀ ψ : GA E N → ℂ, Continuous ψ →
  (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) → (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) →
  (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 → ∀ y ∈ U, ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ η := by
  first | exact @GlobalTheory.CompanionTheory.Conc.translate_sq_mean_close | exact GlobalTheory.CompanionTheory.Conc.translate_sq_mean_close | (intros; apply GlobalTheory.CompanionTheory.Conc.translate_sq_mean_close <;> assumption)
