import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeviPhaseChangeOfVariables
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PhaseApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LeviNorm.integral_phase_sandwich` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIntegralLeviPhaseChangeOfVariables.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.integral_levi_phase_change_of_variables : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ (h : GA D W), GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 → ∀ (a : GL (Fin r) (AE D)) (N : Mx D W.rank r → ℂ), Continuous N → Integrable N μ → Integrable (fun u : Mx D W.rank r => N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val)) μ ∧ ∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val)) u * N u ∂μ = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ W.rank * ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) ∂μ := by
  first | exact @GlobalTheory.LeviNorm.integral_phase_sandwich | exact GlobalTheory.LeviNorm.integral_phase_sandwich | (intros; apply GlobalTheory.LeviNorm.integral_phase_sandwich <;> assumption)
