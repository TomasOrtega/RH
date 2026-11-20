import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.cellConv' : GlobalTheory.CellAmp.CellConv := by
  first | exact @GlobalTheory.CellMaj.cellConv | exact GlobalTheory.CellMaj.cellConv | (intros; apply GlobalTheory.CellMaj.cellConv <;> assumption)
