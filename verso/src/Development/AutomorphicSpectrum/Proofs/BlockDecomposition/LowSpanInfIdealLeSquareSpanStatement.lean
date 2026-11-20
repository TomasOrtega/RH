import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowSpanInfIdealLeSquareSpan
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PresRho.LowMeet.mem_sqSpan_of_mem_lowSpan_of_mem_Jp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLowSpanInfIdealLeSquareSpan.lean&line=129#L129)
-/
theorem _root_.GlobalTheory.T.low_span_inf_ideal_le_square_span : ∀ {n : ℕ} (x : U n), x ∈ lowSpan n → x ∈ Jp n → x ∈ sqSpan n := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.LowMeet.mem_sqSpan_of_mem_lowSpan_of_mem_Jp | exact GlobalTheory.CompanionTheory.PresRho.LowMeet.mem_sqSpan_of_mem_lowSpan_of_mem_Jp | (intros; apply GlobalTheory.CompanionTheory.PresRho.LowMeet.mem_sqSpan_of_mem_lowSpan_of_mem_Jp <;> assumption)
