import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionWhiskerLeftRangePreimageSnd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DualCon.isOpenImmersion_whiskerLeft_left_and_range` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsOpenImmersionWhiskerLeftRangePreimageSnd.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd : ∀ {S : Scheme.{0}} (A : Over S) {B' B : Over S} (j : B' ⟶ B) [IsOpenImmersion j.left], IsOpenImmersion (A ◁ j).left ∧ Set.range (A ◁ j).left = (snd A B).left ⁻¹' Set.range j.left := by
  first | exact @GlobalTheory.DualCon.isOpenImmersion_whiskerLeft_left_and_range | exact GlobalTheory.DualCon.isOpenImmersion_whiskerLeft_left_and_range | (intros; apply GlobalTheory.DualCon.isOpenImmersion_whiskerLeft_left_and_range <;> assumption)
