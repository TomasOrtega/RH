import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AmpleOnGenericFibreOfSemipositive
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Relay.ample_on_generic_fibre_of_semipositive` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FAmpleOnGenericFibreOfSemipositive.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.ample_on_generic_fibre_of_semipositive : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (N A : HermLine J) (a' : K → ℤ) (m p : ℕ), IsSemipositiveH P N → IsSmoothHerm A → (∀ k, 0 < a' k) → 1 ≤ m → 1 ≤ p → (m : ℤ) • A.a = N.a + (p : ℤ) • a' → AmpleOnGenericFibre P A := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ample_on_generic_fibre_of_semipositive | exact GlobalTheory.CompanionTheory.Relay.ample_on_generic_fibre_of_semipositive | (intros; apply GlobalTheory.CompanionTheory.Relay.ample_on_generic_fibre_of_semipositive <;> assumption)
