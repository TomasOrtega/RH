import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfClosedFibreLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FKTrivOfClosedFibreLocalRing.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.kTriv_of_closed_fibre_localRing : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ N : LB B.left, N.IsLB → RelAmple B N → KTriv ((Over.pullback (spMap (IsLocalRing.residue A))).obj B) (N.pull (pullback.fst B.hom (spMap (IsLocalRing.residue A)))) → KTriv B N := by
  first | exact @GlobalTheory.KTrivLocal.kTriv_of_closed_fibre | exact GlobalTheory.KTrivLocal.kTriv_of_closed_fibre | (intros; apply GlobalTheory.KTrivLocal.kTriv_of_closed_fibre <;> assumption)
