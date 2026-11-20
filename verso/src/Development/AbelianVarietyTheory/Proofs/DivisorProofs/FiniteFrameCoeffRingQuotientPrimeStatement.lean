import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFrameCoeffRingQuotientPrime
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
open GlobalTheory.ExpFrame
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrameQuot.finite_quot_prime` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteFrameCoeffRingQuotientPrime.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.finite_frameCoeffRing_quotient_prime : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → Finite (F.O ⧸ Ideal.span {((l : ℕ) : F.O)}) := by
  first | exact @GlobalTheory.FrameQuot.finite_quot_prime | exact GlobalTheory.FrameQuot.finite_quot_prime | (intros; apply GlobalTheory.FrameQuot.finite_quot_prime <;> assumption)
