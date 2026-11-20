import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorSandwichApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncSum
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalFactorSandwichApprox.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.local_factor_sandwich_approx : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (C : ℝ) (g : Fv F v → ℝ), IsStdV v lam → (∀ s, 0 ≤ g s) → GoodFac v lam C g → ∀ η : ℝ, 0 < η → ∃ ψm ψp : Fv F v → ℝ, Continuous ψm ∧ HasCompactSupport ψm ∧ Continuous ψp ∧ HasCompactSupport ψp ∧ (∀ s, 0 ≤ ψm s) ∧ (∀ s, s ≠ 0 → ψm s ≤ g s ∧ g s ≤ ψp s) ∧ 1 - η ≤ ∫ s, ψm s ∂lam ∧ ∫ s, ψp s ∂lam ≤ 1 + η := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.exists_sandwich | exact GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.exists_sandwich | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.exists_sandwich <;> assumption)
