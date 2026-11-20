import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInfiniteScaling
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIInfScaleMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLintegralInfiniteScaling.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.lintegral_infinite_scaling : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (u : κ → ℝ), (∀ j, 0 < u j) →
    ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (f : (κ → AF F) → ℝ≥0∞), ∫⁻ x, f (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) ∂μ =
      (ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F))⁻¹ * ∫⁻ x, f x ∂μ := by
  first | exact @GlobalTheory.TorusTheta.lintegral_infScale_pi | exact GlobalTheory.TorusTheta.lintegral_infScale_pi | (intros; apply GlobalTheory.TorusTheta.lintegral_infScale_pi <;> assumption)
