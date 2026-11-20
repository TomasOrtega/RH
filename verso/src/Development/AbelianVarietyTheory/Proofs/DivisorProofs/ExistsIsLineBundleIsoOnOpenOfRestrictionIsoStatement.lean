import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLineBundleIsoOnOpenOfRestrictionIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PicGlue.isoOn_of_lbIso` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIsLineBundleIsoOnOpenOfRestrictionIso.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.exists_isLineBundleIsoOnOpen_of_restriction_iso : ∀ (X : Scheme.{0}) (W : X.Opens) (L M : LB X), LBIso (L.pull W.ι) (M.pull W.ι) → ∃ w : Cmp W L M, IsoOn W L M w := by
  first | exact @GlobalTheory.PicGlue.isoOn_of_lbIso | exact GlobalTheory.PicGlue.isoOn_of_lbIso | (intros; apply GlobalTheory.PicGlue.isoOn_of_lbIso <;> assumption)
