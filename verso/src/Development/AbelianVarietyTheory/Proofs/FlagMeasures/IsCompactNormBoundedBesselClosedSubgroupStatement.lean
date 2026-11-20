import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactNormBoundedBesselClosedSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsCompactNormBoundedBesselClosedSubgroup.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.isCompact_normBounded_besselClosedSubgroup : ∀ (k r : ℕ) (S : Set (Mat k r)), IsClosedSub k r S → ∀ R : ℝ, IsCompact {g | g ∈ S ∧ opn g ≤ R} := by
  first | exact @GlobalTheory.SgInf.isCompact_normBounded | exact GlobalTheory.SgInf.isCompact_normBounded | (intros; apply GlobalTheory.SgInf.isCompact_normBounded <;> assumption)
