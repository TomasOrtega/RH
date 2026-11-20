import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberZeroOfHorizontal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FVerticalNumberZeroOfHorizontal.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.vertical_number_zero_of_horizontal : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P → ∀ W, divCycle P f W ≠ 0 → (C ϖ : MRing ι O) ∉ W → ∀ l : List (K → ℤ), l.length = d → vNumL W l = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.horizontal_vNumL_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Num.horizontal_vNumL_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.horizontal_vNumL_eq_zero <;> assumption)
