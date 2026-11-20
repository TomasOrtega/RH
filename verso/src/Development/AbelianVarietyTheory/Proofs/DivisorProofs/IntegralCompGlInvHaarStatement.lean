import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompGlInvHaar
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralCompGlInvHaar.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.integral_comp_gl_inv_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (μ : @Measure (Fin n → AE F E) (borel _)), GlobalTheory.SiegelAvg.IsHaarB μ →
    ∀ (t : GL (Fin n) (AE F E)) (f : (Fin n → AE F E) → ℂ),
      (letI : MeasurableSpace (Fin n → AE F E) := borel _; Integrable f μ) →
      (letI : MeasurableSpace (Fin n → AE F E) := borel _;
        ∫ y, f (((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ y) ∂μ) =
        (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) : ℂ) *
          (letI : MeasurableSpace (Fin n → AE F E) := borel _; ∫ y, f y ∂μ) := by
  first | exact @GlobalTheory.SiegelCov.integral_mulVec_inv | exact GlobalTheory.SiegelCov.integral_mulVec_inv | (intros; apply GlobalTheory.SiegelCov.integral_mulVec_inv <;> assumption)
