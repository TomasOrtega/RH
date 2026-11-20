import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSpanPowPDivGroupLevelLe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinrankSpanPowPDivGroupLevelLe.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.finrank_span_pow_pDivGroup_level_le : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), ∀ r : ℕ, Module.finrank K (Submodule.span K (Set.range fun a : G.A r => a ^ p ^ r)) ≤ (p ^ r) ^ Module.finrank K G.dual.omega := by
  first | exact @GlobalTheory.finrank_span_pow_le | exact GlobalTheory.finrank_span_pow_le | (intros; apply GlobalTheory.finrank_span_pow_le <;> assumption)
