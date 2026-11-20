import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentials
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FMongeAmpereIntegralCongrPotentials.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.monge_ampere_integral_congr_potentials : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (U : Set X) (P Q : Fin e → LocPot X) (g g' : X → ℝ), IsNull A Uᶜ → (∀ i, SamePot A U (P i) (Q i)) → (∀ i, ∀ x ∈ U, IsTwiceDifferentiableAt A (Q i) x) → (∀ x ∈ U, g x = g' x) → mInt A P g = mInt A Q g' ∧ (MIntegrable A P g ↔ MIntegrable A Q g') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.mInt_congr_samePot | exact GlobalTheory.CompanionTheory.Ar.PB.mInt_congr_samePot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.mInt_congr_samePot <;> assumption)
