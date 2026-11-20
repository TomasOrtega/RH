import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightSpacesSpan
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CPoly
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.Tope
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RealCount.Tope.iSup_wtDual_eq_top` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDualWeightSpacesSpan.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.dual_weight_spaces_span : ∀ {n : ℕ} (E : KMod n), (⨆ μ, wtDual E μ) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.Tope.iSup_wtDual_eq_top | exact GlobalTheory.CompanionTheory.RealCount.Tope.iSup_wtDual_eq_top | (intros; apply GlobalTheory.CompanionTheory.RealCount.Tope.iSup_wtDual_eq_top <;> assumption)
