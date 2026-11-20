import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeFrobeniusKernelMulSpanPrimePowers
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinrankLeFrobeniusKernelMulSpanPrimePowers.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.finrank_le_frobeniusKernel_mul_span_primePowers : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [Module.Finite K H] (r : ℕ), Module.finrank K H ≤ Module.finrank K (H ⧸ frobKerIdeal (p ^ r) K H) * Module.finrank K (Submodule.span K (Set.range fun a : H => a ^ p ^ r)) := by
  first | exact @GlobalTheory.PDiv.finrank_le_frobKer_mul_span_pow | exact GlobalTheory.PDiv.finrank_le_frobKer_mul_span_pow | (intros; apply GlobalTheory.PDiv.finrank_le_frobKer_mul_span_pow <;> assumption)
