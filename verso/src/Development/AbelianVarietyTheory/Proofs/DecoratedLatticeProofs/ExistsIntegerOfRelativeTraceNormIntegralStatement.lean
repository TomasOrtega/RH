import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegerOfRelativeTraceNormIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SigV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsIntegerOfRelativeTraceNormIntegral.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_integer_of_relative_trace_norm_integral : ∀ (D : D7) (w : D.host.E) (t n : 𝓞 D.host.F), w + D.sp.cm.sig w = algebraMap D.host.F D.host.E t → w * D.sp.cm.sig w = algebraMap D.host.F D.host.E n → ∃ x : 𝓞 D.host.E, (x : D.host.E) = w := by
  first | exact @GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral | exact GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral | (intros; apply GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral <;> assumption)
