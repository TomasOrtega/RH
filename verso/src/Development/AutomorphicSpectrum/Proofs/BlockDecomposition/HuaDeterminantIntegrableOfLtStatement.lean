import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HuaDeterminantIntegrableOfLt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHuaDeterminantIntegrableOfLt.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.hua_determinant_integrable_of_lt : ∀ (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s → ∀ ν : Measure (hermC n), ν.IsAddHaarMeasure →
  Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable <;> assumption)
