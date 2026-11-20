import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalizationPreservesClosedness
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalizationPreservesClosedness.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.localization_preserves_closedness : ∀ {S : Type} [CommRing S] (ϖ : S), (Val ϖ → Loc S ∧ Loc (Localization.Away ϖ)) ∧ (Aic S → Aic (Localization.Away ϖ)) := by
  first | exact @GlobalTheory.CompanionTheory.LocAic.main | exact GlobalTheory.CompanionTheory.LocAic.main | (intros; apply GlobalTheory.CompanionTheory.LocAic.main <;> assumption)
