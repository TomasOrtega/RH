import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDualFourierExpansionSchwartz
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.periodisation_hasSum_fourier_bilinForm` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeDualFourierExpansionSchwartz.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.lattice_dual_fourier_expansion_schwartz : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V), P.Nondegenerate →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : SchwartzMap V ℂ),
    ∃ c : V → ℂ, (∀ N : ℕ, Summable (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        ‖c μ‖ * (1 + ‖(μ : V)‖) ^ N)) ∧
      ∀ x : V, HasSum (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        c μ * Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) (∑' l : Λ, f (x + l)) := by
  first | exact @GlobalTheory.periodisation_hasSum_fourier_bilinForm | exact GlobalTheory.periodisation_hasSum_fourier_bilinForm | (intros; apply GlobalTheory.periodisation_hasSum_fourier_bilinForm <;> assumption)
