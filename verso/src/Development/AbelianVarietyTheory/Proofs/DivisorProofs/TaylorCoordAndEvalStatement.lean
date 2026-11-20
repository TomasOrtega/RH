import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCoordAndEval
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PeriodFamily.taylor_coord_and_eval` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTaylorCoordAndEval.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.taylor_coord_and_taylor_eval_of_prod_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → (∀ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ z i) = t i) ∧ ∀ P : MvPolynomial I ℂ, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ MvPolynomial.eval z P) = MvPolynomial.aeval t P := by
  first | exact @GlobalTheory.PeriodFamily.taylor_coord_and_eval | exact GlobalTheory.PeriodFamily.taylor_coord_and_eval | (intros; apply GlobalTheory.PeriodFamily.taylor_coord_and_eval <;> assumption)
