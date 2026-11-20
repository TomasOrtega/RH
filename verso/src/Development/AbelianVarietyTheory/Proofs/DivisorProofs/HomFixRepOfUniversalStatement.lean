import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixRepOfUniversalAlt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfGroupPullbackDataBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHomFixRepOfUniversalAlt.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.exists_homFixRep_iso_of_universal : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (X : Scheme.{0}) (u : HomGlue.Pt A B L M X), (∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z), ∃! c : Z ⟶ X, u.map hL hM c = x) → ∃ (R : HomFixRep A B L M) (e : R.H ≅ X), e.hom ≫ u.t = R.π := by
  first | exact @GlobalTheory.EndLoc.HomGlue.homFixRep_of_universal | exact GlobalTheory.EndLoc.HomGlue.homFixRep_of_universal | (intros; apply GlobalTheory.EndLoc.HomGlue.homFixRep_of_universal; all_goals assumption)
