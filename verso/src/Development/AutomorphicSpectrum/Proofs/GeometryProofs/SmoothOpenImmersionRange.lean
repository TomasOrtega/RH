import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

/- English proof (translation)
Establish `e : j.opensRange.ι = j.isoOpensRange.inv ≫ j` using `(Iso.eq_inv_comp _).mpr j.isoOpensRange_hom_ι`. Rewrite using `[e, Category.assoc, ← zero_add n]`. Conclude with `smoothOfRelativeDimension_comp 0 n _ _`.
-/
theorem smoothOfRelativeDimension_opensRange_ι_comp
    (A B T : Scheme.{0}) (j : A ⟶ B) [IsOpenImmersion j] (g : B ⟶ T) (n : ℕ)
    (h : SmoothOfRelativeDimension n (j ≫ g)) :
    SmoothOfRelativeDimension n (j.opensRange.ι ≫ g) := by
  have e : j.opensRange.ι = j.isoOpensRange.inv ≫ j :=
    (Iso.eq_inv_comp _).mpr j.isoOpensRange_hom_ι
  rw [e, Category.assoc, ← zero_add n]
  exact smoothOfRelativeDimension_comp 0 n _ _

end GlobalTheory.CompanionTheory.Ar.SncBase
