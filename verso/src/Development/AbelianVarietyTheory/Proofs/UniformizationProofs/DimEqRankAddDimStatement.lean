import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqRankAddDim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
/- English proof (citation)
Apply `GlobalTheory.UT.dim_eq_rank_add_dim` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUniformizationProofs%2FDimEqRankAddDim.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.unif_g_eq_rank_add_g : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => A.g = D.toPre.rank + D.toPre.P.g := by
  first | exact @GlobalTheory.UT.dim_eq_rank_add_dim | exact GlobalTheory.UT.dim_eq_rank_add_dim | (intros; apply GlobalTheory.UT.dim_eq_rank_add_dim <;> assumption)
