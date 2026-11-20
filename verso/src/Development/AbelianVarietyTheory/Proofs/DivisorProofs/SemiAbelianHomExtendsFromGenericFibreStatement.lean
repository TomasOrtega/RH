import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsFromGenericFibre
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Desc.semiAbelian_hom_extend_generic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSemiAbelianHomExtendsFromGenericFibre.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.semiAbelian_hom_extends_from_generic_fibre : ∀ (E : Type) [CommRing E] [IsDomain E] [IsNoetherianRing E] [IsIntegrallyClosed E] (G H : Over (Sp E)) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ f : (Over.pullback (jK E)).obj G ⟶ (Over.pullback (jK E)).obj H, IsMonHom f → ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (jK E)).map F = f := by
  first | exact @GlobalTheory.Desc.semiAbelian_hom_extend_generic | exact GlobalTheory.Desc.semiAbelian_hom_extend_generic | (intros; apply GlobalTheory.Desc.semiAbelian_hom_extend_generic <;> assumption)
