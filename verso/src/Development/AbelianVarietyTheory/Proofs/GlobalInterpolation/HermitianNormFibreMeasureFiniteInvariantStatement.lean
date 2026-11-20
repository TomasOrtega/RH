import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianNormFibreMeasureFiniteInvariant
import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FHermitianNormFibreMeasureFiniteInvariant.lean&line=129#L129)
-/
theorem _root_.GlobalTheory.T.hermitianNormFibreMeasure_finite_invariant : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β : ℝ), IsDxDq fib → β ≠ 0 → IsFiniteMeasureOnCompacts (fib β) ∧ ∀ g : UpqT P Q, (fib β).map (act g) = fib β := by
  first | exact @GlobalTheory.FibreInvariance.fibre_finite_invariant | exact GlobalTheory.FibreInvariance.fibre_finite_invariant | (intros; apply GlobalTheory.FibreInvariance.fibre_finite_invariant <;> assumption)
