import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageTranslatesSeparatedGrp
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsAffineOpenPreimageTranslatesSeparatedGrp.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.isAffineOpen_preimage_translates_separated_grp : ∀ (R' : Type) [CommRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSeparated G'.hom → ∀ (a : 𝟙_ (Over (Sp R')) ⟶ G') (W : G'.left.Opens), IsAffineOpen W → IsAffineOpen ((𝟙 G' * (toUnit G' ≫ a)).left ⁻¹ᵁ W ⊓ (𝟙 G' * (toUnit G' ≫ a⁻¹)).left ⁻¹ᵁ W) := by
  first | exact @GlobalTheory.TransAff.isAffineOpen_translates | exact GlobalTheory.TransAff.isAffineOpen_translates | (intros; apply GlobalTheory.TransAff.isAffineOpen_translates <;> assumption)
