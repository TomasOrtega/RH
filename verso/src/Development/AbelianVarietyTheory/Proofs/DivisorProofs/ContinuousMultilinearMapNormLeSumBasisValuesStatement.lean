import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMultilinearMapNormLeSumBasisValues
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContinuousMultilinearMapNormLeSumBasisValues.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.continuousMultilinearMap_norm_le_sum_basis_values : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (j : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ,
      ‖M‖ ≤ K * ∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖ := by
  first | exact @GlobalTheory.continuousMultilinear_norm_le_basis_sum | exact GlobalTheory.continuousMultilinear_norm_le_basis_sum | (intros; apply GlobalTheory.continuousMultilinear_norm_le_basis_sum <;> assumption)
