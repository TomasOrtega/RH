import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegersBoundedArchimedeanCount
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le | exact GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le | (intros; apply GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.integers_bounded_archimedean_count : ∀ (E : Type) [Field E] [NumberField E], ∃ (C : ℝ) (N : ℕ), ∀ R : ℝ, 1 ≤ R →
    {r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.Finite ∧
    ({r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.ncard : ℝ) ≤ C * R ^ N := by
  first | exact @GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le | exact GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le | (intros; apply GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le <;> assumption)
