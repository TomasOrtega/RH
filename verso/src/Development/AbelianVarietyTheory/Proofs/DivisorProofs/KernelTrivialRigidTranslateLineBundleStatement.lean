import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTrivialRigidTranslateLineBundle
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RigidTranslate.kTriv_rigTransl_any` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKernelTrivialRigidTranslateLineBundle.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.kernelTrivial_rigidTranslateLineBundle : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ a : 𝟙_ (Over S) ⟶ A, Out.KTriv A L → Out.KTriv A (GlobalTheory.RigidTranslate.rigTransl L a) := by
  first | exact @GlobalTheory.RigidTranslate.kTriv_rigTransl_any | exact GlobalTheory.RigidTranslate.kTriv_rigTransl_any | (intros; apply GlobalTheory.RigidTranslate.kTriv_rigTransl_any <;> assumption)
