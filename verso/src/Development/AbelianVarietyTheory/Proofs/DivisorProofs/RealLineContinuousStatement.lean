import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealLineCont.continuous_of_isRealLine` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRealLineContinuous.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.real_line_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : ℝ → GAd σ J), IsRealLine σ J γ → Continuous γ := by
  first | exact @GlobalTheory.RealLineCont.continuous_of_isRealLine | exact GlobalTheory.RealLineCont.continuous_of_isRealLine | (intros; apply GlobalTheory.RealLineCont.continuous_of_isRealLine <;> assumption)
