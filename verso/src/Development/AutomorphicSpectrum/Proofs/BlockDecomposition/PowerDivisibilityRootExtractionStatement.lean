import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowerDivisibilityRootExtraction
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ValPowDvd.dvd_of_pow_mul_dvd_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPowerDivisibilityRootExtraction.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.power_divisibility_root_extraction : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ → ∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z := by
  first | exact @GlobalTheory.CompanionTheory.ValPowDvd.dvd_of_pow_mul_dvd_pow | exact GlobalTheory.CompanionTheory.ValPowDvd.dvd_of_pow_mul_dvd_pow | (intros; apply GlobalTheory.CompanionTheory.ValPowDvd.dvd_of_pow_mul_dvd_pow <;> assumption)
