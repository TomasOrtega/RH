import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsHeisenbergTranslationLaw
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.FlatShiftPf.flatShift | exact GlobalTheory.FlatShiftPf.flatShift | (intros; apply GlobalTheory.FlatShiftPf.flatShift <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.flatMaps_heisenbergTranslation_law : ∀ D : D7, GlobalTheory.FinPl.FlatShift D := by
  first | exact @GlobalTheory.FlatShiftPf.flatShift | exact GlobalTheory.FlatShiftPf.flatShift | (intros; apply GlobalTheory.FlatShiftPf.flatShift <;> assumption)
