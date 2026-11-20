import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralLocalizationAwayInRing
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ValIntClosed.exists_eq_of_isIntegral` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIntegralLocalizationAwayInRing.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.integral_localization_away_in_ring : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ → ∀ x : Localization.Away ϖ, IsIntegral S x → ∃ y : S, algebraMap S (Localization.Away ϖ) y = x := by
  first | exact @GlobalTheory.CompanionTheory.ValIntClosed.exists_eq_of_isIntegral | exact GlobalTheory.CompanionTheory.ValIntClosed.exists_eq_of_isIntegral | (intros; apply GlobalTheory.CompanionTheory.ValIntClosed.exists_eq_of_isIntegral <;> assumption)
