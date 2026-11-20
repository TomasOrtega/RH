import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFunctionCompactRightTranslate
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeightFunctionCompactRightTranslate.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.height_function_compact_right_translate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ C : Set (GAd σ J), IsCompact C → ∃ K : ℝ, 0 ≤ K ∧ ∀ γ g, g ∈ C → h (γ * g) ≤ K * h γ := by
  first | exact @GlobalTheory.EisRes.iwaHt_mul_le_of_isCompact | exact GlobalTheory.EisRes.iwaHt_mul_le_of_isCompact | (intros; apply GlobalTheory.EisRes.iwaHt_mul_le_of_isCompact <;> assumption)
