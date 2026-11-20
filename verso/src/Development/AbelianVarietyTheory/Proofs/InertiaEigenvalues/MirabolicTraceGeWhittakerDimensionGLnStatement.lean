import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicTraceGeWhittakerDimensionGLn
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMirabolicTraceGeWhittakerDimensionGLn.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.mirabolic_trace_ge_whittakerDimension_GLn : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k → ∀ χ : Gn g N → ℂ, IsChar χ → ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (wh ψ χ).re ≤ (tr (eJ g N k s ψ) χ).re := by
  first | exact @GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison | exact GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison | (intros; apply GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison <;> assumption)
