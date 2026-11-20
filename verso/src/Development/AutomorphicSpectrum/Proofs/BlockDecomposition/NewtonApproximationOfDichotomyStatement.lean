import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonApproximationOfDichotomy
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNewtonApproximationOfDichotomy.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.newton_approximation_of_dichotomy : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S ⧸ Ideal.span {ϖ ^ 2}) → Step ϖ := by
  first | exact @GlobalTheory.CompanionTheory.NewtonStep.step_comp | exact GlobalTheory.CompanionTheory.NewtonStep.step_comp | (intros; apply GlobalTheory.CompanionTheory.NewtonStep.step_comp <;> assumption)
