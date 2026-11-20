import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitTranslateBoundedOfFactors
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.adelic_unit_translate_bounded_of_factors : GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.ProductUnitBounded := by
  first | exact @GlobalTheory.RegSS.productUnitBounded | exact GlobalTheory.RegSS.productUnitBounded | (intros; apply GlobalTheory.RegSS.productUnitBounded <;> assumption)
