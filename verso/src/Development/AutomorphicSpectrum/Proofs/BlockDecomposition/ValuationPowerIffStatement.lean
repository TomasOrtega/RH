import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationPowerIff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FValuationPowerIff.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.valuation_power_iff : ∀ {S : Type} [CommRing S] (ϖ : S) (k : ℕ), k ≠ 0 → (Val (ϖ ^ k) ↔ Val ϖ) ∧ (IsAdicComplete (Ideal.span {ϖ ^ k}) S → IsAdicComplete (Ideal.span {ϖ}) S) := by
  first | exact @GlobalTheory.CompanionTheory.PowComp.val_pow | exact GlobalTheory.CompanionTheory.PowComp.val_pow | (intros; apply GlobalTheory.CompanionTheory.PowComp.val_pow <;> assumption)
