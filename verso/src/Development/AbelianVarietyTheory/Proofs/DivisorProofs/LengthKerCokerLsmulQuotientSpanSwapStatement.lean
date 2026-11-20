import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthKerCokerLsmulQuotientSpanSwap
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.kernel_cokernel_length_swap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLengthKerCokerLsmulQuotientSpanSwap.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.length_ker_coker_lsmul_quotient_span_swap : ∀ (A : Type) [CommRing A] [IsDomain A] (a b : A), a ≠ 0 → b ≠ 0 → Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧ Module.length A ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A ((A ⧸ Ideal.span {b}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  first | exact @GlobalTheory.kernel_cokernel_length_swap | exact GlobalTheory.kernel_cokernel_length_swap | (intros; apply GlobalTheory.kernel_cokernel_length_swap <;> assumption)
