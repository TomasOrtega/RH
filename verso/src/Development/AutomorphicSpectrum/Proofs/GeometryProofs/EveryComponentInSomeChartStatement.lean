import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EveryComponentInSomeChart
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FEveryComponentInSomeChart.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.every_component_in_some_chart : ∀ (W P : Scheme.{0}) (Ω : Type) [Field Ω] (ξ' : Sp Ω ⟶ W) (ξ₀ : Sp Ω ⟶ P) (g : W ⟶ P) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → ξ' ≫ g = ξ₀ → ∀ p' : Cpt ξ', ∃ c, InChart ξ' u c p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.exists_inChart_of_comp_eq | exact GlobalTheory.CompanionTheory.Ar.SncBase.exists_inChart_of_comp_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.exists_inChart_of_comp_eq <;> assumption)
