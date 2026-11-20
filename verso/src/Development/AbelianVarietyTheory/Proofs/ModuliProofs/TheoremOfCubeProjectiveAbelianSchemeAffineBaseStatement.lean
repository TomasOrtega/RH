import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubeProjectiveAbelianSchemeAffineBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FTheoremOfCubeProjectiveAbelianSchemeAffineBase.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.theorem_of_cube_projective_abelianScheme_affineBase : Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ M : LB A.left, M.IsLB → Triv (Theta A M) := by
  first | exact @GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy | exact GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy | (intros; apply GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy <;> assumption)
