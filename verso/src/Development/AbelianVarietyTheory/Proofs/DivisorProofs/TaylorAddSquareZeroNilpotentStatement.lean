import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotent
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTaylorAddSquareZeroNilpotent.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.taylor_add_square_zero_nilpotent : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) (n : I → D), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ Ideal.span (Set.range t ∪ Set.range n)) → ∏ a, s a = 0) → (∀ i j, n i * n j = 0) → ∀ f : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → GlobalTheory.PeriodFamily.taylor N (fun i ↦ t i + n i) f = GlobalTheory.PeriodFamily.taylor N t f + ∑ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ fderiv ℂ f z (Pi.single i 1)) * n i := by
  first | exact @GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero | exact GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero | (intros; apply GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero <;> assumption)
