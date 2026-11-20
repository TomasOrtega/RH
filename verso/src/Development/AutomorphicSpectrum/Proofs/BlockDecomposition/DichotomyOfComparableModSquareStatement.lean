import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DichotomyOfComparableModSquare
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDichotomyOfComparableModSquare.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.dichotomy_of_comparable_mod_square : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → (∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) → Dich ϖ := by
  first | exact @GlobalTheory.CompanionTheory.DichMod.dich_of_mod | exact GlobalTheory.CompanionTheory.DichMod.dich_of_mod | (intros; apply GlobalTheory.CompanionTheory.DichMod.dich_of_mod <;> assumption)
