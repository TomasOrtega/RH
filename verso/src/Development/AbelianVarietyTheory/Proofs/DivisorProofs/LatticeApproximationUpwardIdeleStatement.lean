import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeApproximationUpwardIdele.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.real_line_one_parameter_homomorphism : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : ℝ → GAd σ J), IsRealLine σ J γ →
      ∀ s t, γ (s + t) = γ s * γ t := by
  first | exact @GlobalTheory.SiegelSet.isRealLine_add | exact GlobalTheory.SiegelSet.isRealLine_add | (intros; apply GlobalTheory.SiegelSet.isRealLine_add <;> assumption)
