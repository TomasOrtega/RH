import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkSpecializesCompatRingMap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FStalkSpecializesCompatRingMap.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.stalk_specializes_compat_ring_map : ∀ (X : Scheme.{0}) {R W : Type} [CommRing R] [IsLocalRing R] [CommRing W] [IsLocalRing W] (ξ : Sp R ⟶ X) (g : R →+* W) (hs : (spMap g ≫ ξ) (closedPoint W) ⤳ ξ (closedPoint R)) (a : X.presheaf.stalk (ξ (closedPoint R))), (Scheme.stalkClosedPointTo (spMap g ≫ ξ)).hom ((X.presheaf.stalkSpecializes hs).hom a) = g ((Scheme.stalkClosedPointTo ξ).hom a) := by
  first | exact @GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes | exact GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes | (intros; apply GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes <;> assumption)
