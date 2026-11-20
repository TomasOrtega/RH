import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductHuaDeterminantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FProductHuaDeterminantIntegrable.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.product_hua_determinant_integrable : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
  ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
  Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow <;> assumption)
