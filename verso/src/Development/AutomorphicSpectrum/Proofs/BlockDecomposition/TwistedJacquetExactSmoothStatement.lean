import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetExactSmooth
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
open GlobalTheory.PRep GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTwistedJacquetExactSmooth.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.twisted_jacquet_exact_smooth : ∀ {G V₁ V₂ V₃ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) (ρ₃ : Representation ℂ G V₃), IsSmooth ρ₁ → IsSmooth ρ₂ → IsSmooth ρ₃ → ∀ (N : Subgroup G) (θ : N →* ℂˣ), IsOpen (θ.ker : Set N) → (∀ s : Finset G, (↑s : Set G) ⊆ N → ∃ L : Subgroup G, L ≤ N ∧ (↑s : Set G) ⊆ L ∧ IsCompact (L : Set G)) → ∀ (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃) (hf : ∀ x v, f (ρ₁ x v) = ρ₂ x (f v)) (hg : ∀ x v, g (ρ₂ x v) = ρ₃ x (g v)), LinearMap.range f = LinearMap.ker g → LinearMap.range (twMap ρ₁ ρ₂ N θ f hf) = LinearMap.ker (twMap ρ₂ ρ₃ N θ g hg) := by
  first | exact @GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker | exact GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker | (intros; apply GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker <;> assumption)
