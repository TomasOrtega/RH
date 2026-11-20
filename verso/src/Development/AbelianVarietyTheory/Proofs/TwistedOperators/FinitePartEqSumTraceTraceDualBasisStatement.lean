import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartEqSumTraceTraceDualBasis
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFinitePartEqSumTraceTraceDualBasis.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.finitePart_eq_sum_trace_traceDualBasis : ∀ (D : D7), ∃ (d : ℕ) (c e : Fin d → D.host.E), ∀ w : AE D, finPart D w = ∑ l, sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (incA D (c l) * w)) ⊗ₜ[D.host.F] e l := by
  first | exact @GlobalTheory.TwistCoords.finPart_eq_sum_trace | exact GlobalTheory.TwistCoords.finPart_eq_sum_trace | (intros; apply GlobalTheory.TwistCoords.finPart_eq_sum_trace <;> assumption)
