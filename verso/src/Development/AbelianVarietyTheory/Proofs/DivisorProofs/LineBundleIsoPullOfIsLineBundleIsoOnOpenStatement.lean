import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullOfIsLineBundleIsoOnOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLineBundleIsoPullOfIsLineBundleIsoOnOpen.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.lineBundleIso_pull_of_isLineBundleIsoOnOpen : ∀ (X Z : Scheme.{0}) (W : X.Opens) (L M : LB X) (w : Cmp W L M) (r : Z ⟶ X), IsoOn W L M w → (∀ z, r z ∈ W) → LBIso (L.pull r) (M.pull r) := by
  first | exact @GlobalTheory.PicGlue.lbIso_pull_of_isoOn | exact GlobalTheory.PicGlue.lbIso_pull_of_isoOn | (intros; apply GlobalTheory.PicGlue.lbIso_pull_of_isoOn <;> assumption)
