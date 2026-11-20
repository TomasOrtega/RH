import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumAbsNormRpowNegLeDedekindZetaBound
import Formalism.HermitianLattices.StatementMass
open MeasureTheory NumberField Finset
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FSumAbsNormRpowNegLeDedekindZetaBound.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.sum_absNorm_rpow_neg_le_dedekindZeta_bound : ∀ (K : Type) [Field K] [NumberField K] (s : ℝ), 1 < s → ∀ (S : Finset (Ideal (𝓞 K))), (∀ I ∈ S, I ≠ ⊥) → ∑ I ∈ S, (Ideal.absNorm I : ℝ) ^ (-s) ≤ (s / (s - 1)) ^ Module.finrank ℚ K := by
  first | exact @GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le | exact GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le | (intros; apply GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le <;> assumption)
