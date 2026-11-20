import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanInfLogNormEmbeddingEqLogNormDiv
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Formalism.PairingDivisors.StatementH
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.meanInf_log_norm_embedding` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMeanInfLogNormEmbeddingEqLogNormDiv.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.meanInf_log_norm_embedding_eq_log_norm_div : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (a : K), a ≠ 0 → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding a‖) = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / Module.finrank ℚ K := by
  first | exact @GlobalTheory.meanInf_log_norm_embedding | exact GlobalTheory.meanInf_log_norm_embedding | (intros; apply GlobalTheory.meanInf_log_norm_embedding <;> assumption)
