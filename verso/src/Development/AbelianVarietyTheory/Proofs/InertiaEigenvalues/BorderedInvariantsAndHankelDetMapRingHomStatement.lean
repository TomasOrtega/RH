import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedInvariantsAndHankelDetMapRingHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.JR.Step.InvMap.inv_and_Delta_map | exact GlobalTheory.JR.Step.InvMap.inv_and_Delta_map | (intros; apply GlobalTheory.JR.Step.InvMap.inv_and_Delta_map <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.borderedInvariants_and_hankelDet_map_ringHom : ∀ (k k' : Type) [CommRing k] [CommRing k'] (φ : k →+* k') (r : ℕ), (∀ Y : Gl r k, inv (GlobalTheory.JR.Step.glMap φ Y) = (inv Y).map φ) ∧ (∀ a : Inv r k, Delta (a.map φ) = φ (Delta a)) := by
  first | exact @GlobalTheory.JR.Step.InvMap.inv_and_Delta_map | exact GlobalTheory.JR.Step.InvMap.inv_and_Delta_map | (intros; apply GlobalTheory.JR.Step.InvMap.inv_and_Delta_map <;> assumption)
