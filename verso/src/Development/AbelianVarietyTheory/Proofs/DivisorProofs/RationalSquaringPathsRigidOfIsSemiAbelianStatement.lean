import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfIsSemiAbelian
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRationalSquaringPathsRigidOfIsSemiAbelian.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_of_isSemiAbelian : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (F : Type) [Field F] [CharZero F] (b : Sp F ⟶ S), RatRigid G b := by
  first | exact @GlobalTheory.Nef.ratRigid_of_isSemiAbelian | exact GlobalTheory.Nef.ratRigid_of_isSemiAbelian | (intros; apply GlobalTheory.Nef.ratRigid_of_isSemiAbelian <;> assumption)
