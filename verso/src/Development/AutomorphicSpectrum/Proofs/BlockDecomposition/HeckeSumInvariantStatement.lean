import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSumInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHeckeSumInvariant.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.hecke_sum_invariant : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ), (Function.support fun q : G ⧸ K => f q.out).Finite → (∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → ∀ v : V, (∀ k ∈ K, ρ k v = v) → ∀ k ∈ K, ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v) = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v := by
  first | exact @GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed | exact GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed | (intros; apply GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed <;> assumption)
