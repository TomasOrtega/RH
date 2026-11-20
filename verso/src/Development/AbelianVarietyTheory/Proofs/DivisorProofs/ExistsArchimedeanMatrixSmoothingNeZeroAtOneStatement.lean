import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanMatrixSmoothingNeZeroAtOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsArchimedeanMatrixSmoothingNeZeroAtOne.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_archimedeanMatrixSmoothing_ne_zero_at_one : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (W : GL (Fin n) (Cinf E) → ℂ), Continuous W → W 1 ≠ 0 → ∃ α : (Fin n → Fin n → Cinf E) → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ tsupport α ⊆ {x | IsUnit (Matrix.of x)} ∧ smoothMatInf α W 1 ≠ 0 := by
  first | exact @GlobalTheory.JSW.MirCinf.exists_smoothMatInf_ne_zero_at_one | exact GlobalTheory.JSW.MirCinf.exists_smoothMatInf_ne_zero_at_one | (intros; apply GlobalTheory.JSW.MirCinf.exists_smoothMatInf_ne_zero_at_one <;> assumption)
