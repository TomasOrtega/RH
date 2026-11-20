import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTensorPowers
import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.locNormPow_tensorPowers` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLocalNormalisationTensorPowers.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.localNormalisation_tensorPowers : Formalism.L2.AlgTh.LocNormPow := by
  first | exact @GlobalTheory.locNormPow_tensorPowers | exact GlobalTheory.locNormPow_tensorPowers | (intros; apply GlobalTheory.locNormPow_tensorPowers <;> assumption)
