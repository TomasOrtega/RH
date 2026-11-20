import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFieldsBaseChangeIsFieldIff
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.RegSS.tensorFieldIff | exact GlobalTheory.RegSS.tensorFieldIff | (intros; apply GlobalTheory.RegSS.tensorFieldIff <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.product_fields_baseChange_isField_iff : GlobalTheory.RegSS.TensorFieldIff := by
  first | exact @GlobalTheory.RegSS.tensorFieldIff | exact GlobalTheory.RegSS.tensorFieldIff | (intros; apply GlobalTheory.RegSS.tensorFieldIff <;> assumption)
