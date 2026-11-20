import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightSupportBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SignChain.gam_support` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSignConeWeightSupportBound.lean&line=344#L344)
-/
theorem _root_.GlobalTheory.T.sign_cone_weight_support_bound : ∀ m : ℕ, ∀ (y : (Fin m → SignType) → ℝ) (M : ℝ) a, (∀ e, |y e| ≤ M) → gam y a ≠ 0 → ∀ i, |a i| ≤ 2 * M := by
  first | exact @GlobalTheory.CompanionTheory.SignChain.gam_support | exact GlobalTheory.CompanionTheory.SignChain.gam_support | (intros; apply GlobalTheory.CompanionTheory.SignChain.gam_support <;> assumption)
