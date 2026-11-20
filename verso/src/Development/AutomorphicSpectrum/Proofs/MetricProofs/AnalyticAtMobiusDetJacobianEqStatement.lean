import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticAtMobiusDetJacobianEq
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffAtFrameEntry
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FAnalyticAtMobiusDetJacobianEq.lean&line=104#L104)
-/
theorem _root_.GlobalTheory.T.analyticAt_mobius_det_jacobian_eq : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ), (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a : ℂ), GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a ≠ 0 → AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y) ∧ (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y)).det = GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibPt.analyticAt_mobius_and_det_jacobian | exact GlobalTheory.CompanionTheory.Ar.PB.FibPt.analyticAt_mobius_and_det_jacobian | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibPt.analyticAt_mobius_and_det_jacobian <;> assumption)
