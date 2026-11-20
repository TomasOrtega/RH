import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfSmoothGeomIrreducibleOverModificatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsIntegralOfSmoothGeomIrreducibleOverModificatio.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.isIntegral_of_smooth_geomIrreducible_over_modification : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → GeometricallyIrreducible G.hom → Nonempty G.left → IsIntegral G.left := by
  first | exact @GlobalTheory.MumInt.isIntegral_of_smooth | exact GlobalTheory.MumInt.isIntegral_of_smooth | (intros; apply GlobalTheory.MumInt.isIntegral_of_smooth <;> assumption)
