import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedUnitCoefficientRoot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.UnitRoot.exists_root` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAbsolutelyClosedUnitCoefficientRoot.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.absolutely_closed_unit_coefficient_root : ∀ {S : Type} [CommRing S] , Aic S → (∀ a b : S, IsUnit (a + b) → IsUnit a ∨ IsUnit b) → ∀ (Q : Polynomial S) (i : ℕ), Q.coeff 0 = 1 → 0 < i → IsUnit (Q.coeff i) → ∃ y, Q.eval y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.UnitRoot.exists_root | exact GlobalTheory.CompanionTheory.UnitRoot.exists_root | (intros; apply GlobalTheory.CompanionTheory.UnitRoot.exists_root <;> assumption)
