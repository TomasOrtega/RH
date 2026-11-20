import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleSurjectiveLocalSection
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.EtaleSections.exists_secOn_of_etale_surjective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEtaleSurjectiveLocalSection.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.etale_surjective_local_section : ∀ {S : Type} [CommRing S] , Aic S → Loc S → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), Etale f → Surjective f → ∀ m : Ideal S, m.IsMaximal → ∃ e : S, IsIdempotentElem e ∧ e ∉ m ∧ SecOn f e := by
  first | exact @GlobalTheory.CompanionTheory.EtaleSections.exists_secOn_of_etale_surjective | exact GlobalTheory.CompanionTheory.EtaleSections.exists_secOn_of_etale_surjective | (intros; apply GlobalTheory.CompanionTheory.EtaleSections.exists_secOn_of_etale_surjective <;> assumption)
