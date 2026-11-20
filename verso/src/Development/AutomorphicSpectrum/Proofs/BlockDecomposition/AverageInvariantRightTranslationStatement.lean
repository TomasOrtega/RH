import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariantRightTranslation
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAverageInvariantRightTranslation.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.average_invariant_right_translation : ∀ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) (ϖ : O) (φ : GL (Ix n) O → ℂ),
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∀ j : GL (Ix n) O,
      avgK ϖ (fun κ => φ (κ * j)) = avgK ϖ φ := by
  first | exact @GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant | exact GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant | (intros; apply GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant <;> assumption)
