import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NormSum.exists_integer_map_eq_w0` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsIntegerMapEqHalfOneAddSqrt.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.exists_integer_map_eq_halfOneAddSqrt : ∀ (D : D7), ∃ a : 𝓞 D.host.K, D.host.φ₀ (((a : D.host.K) : D.host.E)) = w0 D := by
  first | exact @GlobalTheory.NormSum.exists_integer_map_eq_w0 | exact GlobalTheory.NormSum.exists_integer_map_eq_w0 | (intros; apply GlobalTheory.NormSum.exists_integer_map_eq_w0 <;> assumption)
