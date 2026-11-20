import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
open MeasureTheory Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FHaarUpqIsMulRightInvariant.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.haar_upq_is_mul_right_invariant : ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure | exact GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure | (intros; apply GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure <;> assumption)
