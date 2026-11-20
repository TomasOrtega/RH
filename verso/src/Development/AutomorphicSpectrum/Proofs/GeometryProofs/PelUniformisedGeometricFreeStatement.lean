import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PelUniformisedGeometricFree
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Unif.geomPF_closedPoint` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FPelUniformisedGeometricFree.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.pel_uniformised_geometric_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (_ : PELUnif (IsLocalRing.maximalIdeal R) t), GeomPF t (spMap (IsLocalRing.residue R)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Unif.geomPF_closedPoint | exact GlobalTheory.CompanionTheory.Ar.Unif.geomPF_closedPoint | (intros; apply GlobalTheory.CompanionTheory.Ar.Unif.geomPF_closedPoint <;> assumption)
