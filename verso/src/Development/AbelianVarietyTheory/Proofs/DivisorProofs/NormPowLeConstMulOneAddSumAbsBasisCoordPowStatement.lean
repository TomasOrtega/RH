import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPowLeConstMulOneAddSumAbsBasisCoordPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormPowLeConstMulOneAddSumAbsBasisCoordPow.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.norm_pow_le_const_mul_one_add_sum_abs_basisCoord_pow : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (i : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : E, ‖x‖ ^ i ≤ K * (1 + ∑ c, |b.coord c x| ^ i) := by
  first | exact @GlobalTheory.norm_pow_le_const_mul_one_add_sum_abs_coord_pow | exact GlobalTheory.norm_pow_le_const_mul_one_add_sum_abs_coord_pow | (intros; apply GlobalTheory.norm_pow_le_const_mul_one_add_sum_abs_coord_pow <;> assumption)
