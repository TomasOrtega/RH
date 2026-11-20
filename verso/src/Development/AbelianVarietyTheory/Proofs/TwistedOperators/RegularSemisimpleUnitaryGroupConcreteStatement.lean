import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleUnitaryGroupConcrete
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.RegSSObj.regularSemisimple | exact GlobalTheory.RegSSObj.regularSemisimple | (intros; apply GlobalTheory.RegSSObj.regularSemisimple <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.regularSemisimple_unitaryGroup_concrete : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple := by
  first | exact @GlobalTheory.RegSSObj.regularSemisimple | exact GlobalTheory.RegSSObj.regularSemisimple | (intros; apply GlobalTheory.RegSSObj.regularSemisimple <;> assumption)
