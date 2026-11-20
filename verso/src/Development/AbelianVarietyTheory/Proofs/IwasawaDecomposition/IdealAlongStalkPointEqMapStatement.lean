import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongStalkPointEqMap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIdealAlongStalkPointEqMap.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.ideal_along_stalk_point_eq_map : ∀ (T : Scheme.{0}) (v : T) (J : T.IdealSheafData) (W : Type) [CommRing W] [IsLocalRing W] (g : T.presheaf.stalk v →+* W), IsLocalHom g → idlAlong J (spMap g ≫ T.fromSpecStalk v) = (FinalTheorems.stalkId J v).map g := by
  first | exact @GlobalTheory.TraitStalk.idlAlong_spMap_fromSpecStalk | exact GlobalTheory.TraitStalk.idlAlong_spMap_fromSpecStalk | (intros; apply GlobalTheory.TraitStalk.idlAlong_spMap_fromSpecStalk <;> assumption)
