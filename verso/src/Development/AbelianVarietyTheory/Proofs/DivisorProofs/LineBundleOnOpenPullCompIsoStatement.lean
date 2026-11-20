import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleOnOpenPullCompIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLineBundleOnOpenPullCompIso.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.lineBundleOnOpen_pull_comp_iso : ∀ (X Z Z' : Scheme.{0}) (W : X.Opens) (L : LB X) (r : Z ⟶ X) (s : Z' ⟶ Z), IsOn W L → (∀ z, r z ∈ W) → LBIso ((L.pull r).pull s) (L.pull (s ≫ r)) := by
  first | exact @GlobalTheory.PicGlue.isOn_pull_comp | exact GlobalTheory.PicGlue.isOn_pull_comp | (intros; apply GlobalTheory.PicGlue.isOn_pull_comp <;> assumption)
