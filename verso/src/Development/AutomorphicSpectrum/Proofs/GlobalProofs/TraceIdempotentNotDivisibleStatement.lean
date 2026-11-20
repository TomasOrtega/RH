import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TraceIdempotentNotDivisible

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FTraceIdempotentNotDivisible.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.trace_idempotent_not_divisible : ∀ (B : Type) [CommRing B] [Module.Free ℤ B] [Module.Finite ℤ B] (x : B) (p m : ℕ), p.Prime → Module.finrank ℤ B < p ^ m → x * x - x ∈ Ideal.span {((p : B)) ^ m} → x ∉ Ideal.span {((p : B)) ^ m} → ¬ ((p : ℤ) ^ m ∣ Algebra.trace ℤ B x) := by
  first | exact @GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace | exact GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace | (intros; apply GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace <;> assumption)
