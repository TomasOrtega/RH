import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundlePullOfIsLineBundleOnOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PicGlue.pull_isLB_of_isOn` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsLineBundlePullOfIsLineBundleOnOpen.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.isLineBundle_pull_of_isLineBundleOnOpen : ∀ (X Z : Scheme.{0}) (W : X.Opens) (L : LB X) (r : Z ⟶ X), IsOn W L → (∀ z, r z ∈ W) → (L.pull r).IsLB := by
  first | exact @GlobalTheory.PicGlue.pull_isLB_of_isOn | exact GlobalTheory.PicGlue.pull_isLB_of_isOn | (intros; apply GlobalTheory.PicGlue.pull_isLB_of_isOn <;> assumption)
