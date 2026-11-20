import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRemainderIsBigOAndTaylorFlat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PeriodFamily.taylor_remainder_and_flat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTaylorRemainderIsBigOAndTaylorFlat.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.taylorRemainder_isBigO_and_taylor_flat : ∀ {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → ((fun z ↦ f z - GlobalTheory.PeriodFamily.taylor N z f) =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) ∧ ((f =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) → ∀ {D : Type} [CommRing D] [Algebra ℂ D] (t : I → D), GlobalTheory.PeriodFamily.taylor N t f = 0) := by
  first | exact @GlobalTheory.PeriodFamily.taylor_remainder_and_flat | exact GlobalTheory.PeriodFamily.taylor_remainder_and_flat | (intros; apply GlobalTheory.PeriodFamily.taylor_remainder_and_flat <;> assumption)
