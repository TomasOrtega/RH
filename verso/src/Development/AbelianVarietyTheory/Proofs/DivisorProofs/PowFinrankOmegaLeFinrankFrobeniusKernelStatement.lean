import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankOmegaLeFinrankFrobeniusKernel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPowFinrankOmegaLeFinrankFrobeniusKernel.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.pow_finrank_omega_le_finrank_frobeniusKernel : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), ∀ r : ℕ, (p ^ r) ^ Module.finrank K G.omega ≤ Module.finrank K (G.A r ⧸ frobKerIdeal (p ^ r) K (G.A r)) := by
  first | exact @GlobalTheory.PDivGroup.pow_finrank_omega_le_finrank_frobKer | exact GlobalTheory.PDivGroup.pow_finrank_omega_le_finrank_frobKer | (intros; apply GlobalTheory.PDivGroup.pow_finrank_omega_le_finrank_frobKer <;> assumption)
