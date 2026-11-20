import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitSubtorusOfIdempotentFamily
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.split_subtorus_of_idempotent_family : GlobalTheory.RegSS.SubtorusOfIdempotents := by
  first | exact @GlobalTheory.RegSS.IdemTorus.subtorusOfIdempotents | exact GlobalTheory.RegSS.IdemTorus.subtorusOfIdempotents | (intros; apply GlobalTheory.RegSS.IdemTorus.subtorusOfIdempotents <;> assumption)
