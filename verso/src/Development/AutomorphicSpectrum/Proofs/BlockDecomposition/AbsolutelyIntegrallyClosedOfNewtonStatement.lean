import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyIntegrallyClosedOfNewton
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAbsolutelyIntegrallyClosedOfNewton.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.absolutely_integrally_closed_of_newton : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S], Step ϖ → (∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z) → Aic S := by
  first | exact @GlobalTheory.CompanionTheory.AicLimit.aic_of_step | exact GlobalTheory.CompanionTheory.AicLimit.aic_of_step | (intros; apply GlobalTheory.CompanionTheory.AicLimit.aic_of_step <;> assumption)
