import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechLineBundleAmbientOfOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCechLineBundleAmbientOfOpenImmersion.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.exists_cech_lineBundle_ambient_of_openImmersion : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X'), L.IsLB → ∃ L' : LB X, IsOn f.opensRange L' ∧ LBIso (L'.pull f) L := by
  first | exact @GlobalTheory.PicGlue.exists_isOn_of_openImmersion | exact GlobalTheory.PicGlue.exists_isOn_of_openImmersion | (intros; apply GlobalTheory.PicGlue.exists_isOn_of_openImmersion <;> assumption)
