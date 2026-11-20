import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationIntertwinerPrimeIndex
import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLocalNormalisationIntertwinerPrimeIndex.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.localNormalisation_intertwiner_prime_index : Formalism.L2.AlgTh.LocNormInter := by
  first | exact @GlobalTheory.locNormInter | exact GlobalTheory.locNormInter | (intros; apply GlobalTheory.locNormInter <;> assumption)
