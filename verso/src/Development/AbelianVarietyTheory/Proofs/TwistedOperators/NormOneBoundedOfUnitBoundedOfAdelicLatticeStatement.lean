import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneBoundedOfUnitBoundedOfAdelicLattice
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FNormOneBoundedOfUnitBoundedOfAdelicLattice.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.normOfUnitBounded_of_tensorLattice' : GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.NormOfUnitBounded := by
  first | exact @GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice | exact GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice | (intros; apply GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice <;> assumption)
