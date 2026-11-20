import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibrePowerFreePullback
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FFibrePowerFreePullback.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.fibre_power_free_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (X₂ : Scheme.{0}) (t₂ : SAB H X₂) (f : X₂ ⟶ X0) (_ : SABMap t₂ t f) (z : X₂), FibPF t₂ z ↔ FibPF t (f z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FibPull.fibPF_pull_iff | exact GlobalTheory.CompanionTheory.Ar.FibPull.fibPF_pull_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.FibPull.fibPF_pull_iff <;> assumption)
