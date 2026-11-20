import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.anSys_open_basics` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FAnalyticSystemRegularityProperties.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.analytic_system_regularity_properties : ∀ (e : ℕ) (σ : Type) (S : AnSys e σ), IsOpen S.open' ∧ IsNull S.A S.open'ᶜ ∧ (∀ a, ∀ x ∈ S.open', IsTwiceDifferentiableAt S.A (S.potH a) x) ∧ (∀ a t, 0 < t → t ≤ S.t₀ → IsPotential S.A (S.potT a t)) ∧ ∀ y ∈ S.open', Real.exp 1 ≤ rW S.L S.s y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.anSys_open_basics | exact GlobalTheory.CompanionTheory.Ar.PB.anSys_open_basics | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.anSys_open_basics <;> assumption)
