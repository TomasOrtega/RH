import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorGeneratedAlgebraStructure
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.RegSS.CycAlg.cyclicAlgebra | exact GlobalTheory.RegSS.CycAlg.cyclicAlgebra | (intros; apply GlobalTheory.RegSS.CycAlg.cyclicAlgebra <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.cyclicVector_generatedAlgebra_structure : GlobalTheory.RegSS.CyclicAlgebra := by
  first | exact @GlobalTheory.RegSS.CycAlg.cyclicAlgebra | exact GlobalTheory.RegSS.CycAlg.cyclicAlgebra | (intros; apply GlobalTheory.RegSS.CycAlg.cyclicAlgebra <;> assumption)
