import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddingsMatchInfinitePlacesAutInstance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.RadCov.Place.placeMatch | exact GlobalTheory.RadCov.Place.placeMatch | (intros; apply GlobalTheory.RadCov.Place.placeMatch <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.embeddingsMatchInfinitePlaces_autInstance : ∀ (I : AutInst) (xf : I.Gf), PlaceMatch I.φ I.P (frm I (1, xf)) := by
  first | exact @GlobalTheory.RadCov.Place.placeMatch | exact GlobalTheory.RadCov.Place.placeMatch | (intros; apply GlobalTheory.RadCov.Place.placeMatch <;> assumption)
