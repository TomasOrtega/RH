import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidDescendsFieldMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRationalSquaringPathsRigidDescendsFieldMap.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_descends_field_map : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (F Ω : Type) [Field F] [Field Ω] (φ : F →+* Ω) (b : Sp F ⟶ S), RatRigid G (spMap φ ≫ b) → RatRigid G b := by
  first | exact @GlobalTheory.Nef.ratRigid_of_field_map | exact GlobalTheory.Nef.ratRigid_of_field_map | (intros; apply GlobalTheory.Nef.ratRigid_of_field_map <;> assumption)
