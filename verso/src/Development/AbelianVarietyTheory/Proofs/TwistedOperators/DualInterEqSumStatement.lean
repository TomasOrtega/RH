import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualInterEqSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FDualInterEqSum.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.dual_inter_eq_sum' : Dual := by
  first | exact @GlobalTheory.InertZeta.dual_inter_eq_sum | exact GlobalTheory.InertZeta.dual_inter_eq_sum | (intros; apply GlobalTheory.InertZeta.dual_inter_eq_sum <;> assumption)
