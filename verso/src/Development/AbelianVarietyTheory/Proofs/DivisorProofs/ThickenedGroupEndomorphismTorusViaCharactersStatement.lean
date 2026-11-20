import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedGroupEndomorphismTorusViaCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThickenedGroupEndomorphismTorusViaCharacters.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.thickenedGroup_endomorphism_torus_via_characters : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∀ (F : thickObj R I e G ⟶ thickObj R I e G), IsCoordEnd g a a' h' u F → ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X, TorusEndOf D.X h' t ∧ g.i ≫ F = t ≫ g.i := by
  first | exact @GlobalTheory.Mum.EndThick.torus_of_isCoordEnd | exact GlobalTheory.Mum.EndThick.torus_of_isCoordEnd | (intros; apply GlobalTheory.Mum.EndThick.torus_of_isCoordEnd <;> assumption)
