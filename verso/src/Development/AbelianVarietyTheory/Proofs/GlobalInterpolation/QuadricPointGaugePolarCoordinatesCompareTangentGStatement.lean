import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadricPointGaugePolarCoordinatesCompareTangentG
import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolarCompare.polar_compare` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FQuadricPointGaugePolarCoordinatesCompareTangentG.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.quadricPointGauge_polarCoordinates_compare_tangentGauge : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u : ℝ × Sp P' Q', u.1 ∈ Set.Ioo (-Real.pi) Real.pi → (tanGauge u < t⁻¹ * r → ptGauge e (polarPt e u) < r) ∧ (ptGauge e (polarPt e u) < r → tanGauge u < t * r) := by
  first | exact @GlobalTheory.PolarCompare.polar_compare | exact GlobalTheory.PolarCompare.polar_compare | (intros; apply GlobalTheory.PolarCompare.polar_compare <;> assumption)
