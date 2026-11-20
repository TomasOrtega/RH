import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambda
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
Apply `GlobalTheory.PointTranslate.exists_point_cls_eq_lam` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPointPicardClassEqTranslateOfTrivialLambda.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.exists_point_picardClass_eq_translate_of_trivial_lambda : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left) (hL : L.IsLB), Out.KTriv B L → ∀ (O : LB B.left) (hO : O.IsLB), lam (cls O hO) (fst B B) (snd B B) = 0 → ∃ x : 𝟙_ (Over (Sp K)) ⟶ B, cls O hO = lam (cls L hL) (toUnit B ≫ x) (𝟙 B) := by
  first | exact @GlobalTheory.PointTranslate.exists_point_cls_eq_lam | exact GlobalTheory.PointTranslate.exists_point_cls_eq_lam | (intros; apply GlobalTheory.PointTranslate.exists_point_cls_eq_lam <;> assumption)
