import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTwoSidedHaarOfLeftInvariantProbabilityCompact
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsTwoSidedHaarOfLeftInvariantProbabilityCompact.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.isTwoSidedHaar_of_leftInvariant_probability_compactUnitary : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ → μ Set.univ = 1 → B.IsHaarOn (UWset k r z) μ := by
  first | exact @GlobalTheory.ThA.haarW_twoSided_of_left | exact GlobalTheory.ThA.haarW_twoSided_of_left | (intros; apply GlobalTheory.ThA.haarW_twoSided_of_left <;> assumption)
