import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalFixedTensor
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteDimensionalFixedTensor.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.finiteDimensional_fixed_tensor : ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (K₁ : Subgroup G) (K₂ : Subgroup H), FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K₁) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K₂) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed (GlobalTheory.SmGL.extTensor ρ σ) (K₁.prod K₂)) := by
  first | exact @GlobalTheory.CompanionTheory.ExtTensorFixed.finiteDimensional_fixed_extTensor | exact GlobalTheory.CompanionTheory.ExtTensorFixed.finiteDimensional_fixed_extTensor | (intros; apply GlobalTheory.CompanionTheory.ExtTensorFixed.finiteDimensional_fixed_extTensor <;> assumption)
