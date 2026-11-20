import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenAffineOpenMeetingFibresGrpScheme
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsBasicOpenAffineOpenMeetingFibresGrpScheme.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_basicOpen_affineOpen_meeting_fibres_grpScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (s : Sp R), ∃ f : R, s ∈ Set.range (spMap (algebraMap R (Localization.Away f))) ∧ ∃ W : A.left.Opens, IsAffineOpen W ∧ ∀ t ∈ Set.range (spMap (algebraMap R (Localization.Away f))), ∃ x ∈ W, A.hom x = t := by
  first | exact @GlobalTheory.chartAroundUnit | exact GlobalTheory.chartAroundUnit | (intros; apply GlobalTheory.chartAroundUnit <;> assumption)
