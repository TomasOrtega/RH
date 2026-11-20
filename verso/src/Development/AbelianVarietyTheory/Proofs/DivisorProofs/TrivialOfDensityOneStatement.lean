import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialOfDensityOne
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TrivialOfDensityOne
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DensityOneTriv.trivialOfDensityOne` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTrivialOfDensityOne.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.trivial_of_density_one : GlobalTheory.IndefiniteRowSideFullHecke.TrivialOfDensityOneCharacters.TrivialOfDensityOne := by
  first | exact @GlobalTheory.DensityOneTriv.trivialOfDensityOne | exact GlobalTheory.DensityOneTriv.trivialOfDensityOne | (intros; apply GlobalTheory.DensityOneTriv.trivialOfDensityOne <;> assumption)
