import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SabMapId
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.exists_sabMap_id` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FSabMapId.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.sab_map_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S), ∃ m : SABMap t t (𝟙 S), m.φ = 𝟙 t.G.left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_sabMap_id | exact GlobalTheory.CompanionTheory.Ar.exists_sabMap_id | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_sabMap_id <;> assumption)
