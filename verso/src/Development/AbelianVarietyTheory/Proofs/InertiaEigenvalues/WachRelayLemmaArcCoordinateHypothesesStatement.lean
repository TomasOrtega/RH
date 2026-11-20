import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachRelayLemmaArcCoordinateHypotheses
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWachRelayLemmaArcCoordinateHypotheses.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.wachRelayLemma_arcCoordinateHypotheses : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.RelayArcLifting D HW F ∧ UnusedSlot80.AdmArcA D HW F Cm := by
  first | exact @GlobalTheory.NQ.relay_and_arc_inputs | exact GlobalTheory.NQ.relay_and_arc_inputs | (intros; apply GlobalTheory.NQ.relay_and_arc_inputs <;> assumption)
