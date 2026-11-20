import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericEndomorphismExtends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSemiAbelianGenericEndomorphismExtends.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.semiAbelian_generic_endomorphism_extends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ f : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom f → ∃ g : G ⟶ G, IsMonHom g ∧ (Over.pullback (jK R)).map g = f := by
  first | exact @GlobalTheory.Mum.genericEnd_extends | exact GlobalTheory.Mum.genericEnd_extends | (intros; apply GlobalTheory.Mum.genericEnd_extends <;> assumption)
