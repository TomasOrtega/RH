import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedPolynomialSplits
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAbsolutelyClosedPolynomialSplits.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.absolutely_closed_polynomial_splits : ∀ {S : Type} [CommRing S] , Aic S → ∀ P : Polynomial S, P.Monic → ∃ s : Multiset S, P = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  first | exact @GlobalTheory.CompanionTheory.MonicSplit.monic_splits | exact GlobalTheory.CompanionTheory.MonicSplit.monic_splits | (intros; apply GlobalTheory.CompanionTheory.MonicSplit.monic_splits <;> assumption)
