import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesFlatLift
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FPublishedTheorems%2FNadelVanishingPairs%2FNadelVanishingLemmas%2FEtaleCoordinatesFlatLift.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.etale_coordinates_flat_lift : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y), IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → ∀ (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ y : X, π y ∈ U → IsFlatLift p (π.stalkMap y).hom := by
  first | exact @_root_.GlobalTheory.DI.isFlatLift_stalkMap_of_isEtCoord | exact _root_.GlobalTheory.DI.isFlatLift_stalkMap_of_isEtCoord | (intros; apply _root_.GlobalTheory.DI.isFlatLift_stalkMap_of_isEtCoord <;> assumption)
