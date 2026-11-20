import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.PointwiseOfSpanHeisenberg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.InertLen.pointwise` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FPointwiseOfSpanHeisenberg.lean&line=172#L172)
-/
theorem _root_.GlobalTheory.T.pointwise_of_span_heisenberg : AddVec → Dual → SpanEq → Heis → Pointwise := by
  first | exact @GlobalTheory.CompanionTheory.InertLen.pointwise | exact GlobalTheory.CompanionTheory.InertLen.pointwise | (intros; apply GlobalTheory.CompanionTheory.InertLen.pointwise <;> assumption)
