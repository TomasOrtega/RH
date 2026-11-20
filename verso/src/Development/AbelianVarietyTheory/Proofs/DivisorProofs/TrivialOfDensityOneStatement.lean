import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialOfDensityOne
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TrivialOfDensityOne
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.DensityOneTriv.trivialOfDensityOne | exact GlobalTheory.DensityOneTriv.trivialOfDensityOne | (intros; apply GlobalTheory.DensityOneTriv.trivialOfDensityOne <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.trivial_of_density_one : GlobalTheory.IndefiniteRowSideFullHecke.TrivialOfDensityOneCharacters.TrivialOfDensityOne := by
  first | exact @GlobalTheory.DensityOneTriv.trivialOfDensityOne | exact GlobalTheory.DensityOneTriv.trivialOfDensityOne | (intros; apply GlobalTheory.DensityOneTriv.trivialOfDensityOne <;> assumption)
