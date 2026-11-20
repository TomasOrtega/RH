import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenMeetingFibresPullbackSpecRingHom
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAffineOpenMeetingFibresPullbackSpecRingHom.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.affineOpen_meeting_fibres_pullback_specRingHom : ∀ {R R' : Type} [CommRing R] [CommRing R'] (a : R →+* R') (A : Over (Sp R)) (W : A.left.Opens), IsAffineOpen W → (∀ t ∈ Set.range (spMap a), ∃ x ∈ W, A.hom x = t) → ∃ V : ((Over.pullback (spMap a)).obj A).left.Opens, IsAffineOpen V ∧ ∀ s : Sp R', ∃ x ∈ V, ((Over.pullback (spMap a)).obj A).hom x = s := by
  first | exact @GlobalTheory.affine_preimage_pullback_meets_fibres | exact GlobalTheory.affine_preimage_pullback_meets_fibres | (intros; apply GlobalTheory.affine_preimage_pullback_meets_fibres <;> assumption)
