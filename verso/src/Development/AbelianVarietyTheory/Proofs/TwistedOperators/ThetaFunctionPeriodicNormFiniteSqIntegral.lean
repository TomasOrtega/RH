import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PhaseApply
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSqInt

/- English proof (translation)
Introduce `D ψ hψ S T μ 𝓕 hC F hF`. Use `haveI hB : BorelSpace (WO S T) := ⟨rfl⟩`. Use `haveI hO : OpensMeasurableSpace (WO S T) := BorelSpace.opensMeasurable`. Establish `hn : ∀ x, ‖ψ x‖ = 1` using `hψ.1.2.1`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `γ hγ w`. Take `⟨ξ, rfl⟩` from `hγ`. Establish `hq` using `hF.quasi ξ w`. Establish `e : ((incA D).toAddMonoidHom.mapMatrix ξ : WO S T) = ratW T S ξ` using `rfl`. Rewrite using `[e, hq, norm_mul, hn, one_mul]`.

Take `⟨M, hM⟩` from `GlobalTheory.OrientedHeis.theta_bounded hψ hF`. Establish `hle : ∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ ≤ ∫⁻ _x in 𝓕, ENNReal.ofReal M ^ 2 ∂μ`. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Use `gcongr`. Rewrite using `[← ofReal_norm_eq_enorm]`.

Conclude with `ENNReal.ofReal_le_ofReal (hM x)`. Rewrite `hle` using `[setLIntegral_const, hC.2.2, mul_one]`. Conclude with `ne_top_of_le_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hle`. Establish `h1 : ∀ x, F x * starRingEnd ℂ (F x) = (((‖F x‖ ^ 2 : ℝ)) : ℂ)` using `fun x => by`. Rewrite using `[Complex.mul_conj']`.

Use `push_cast`. Both sides reduce to the same expression. Repeatedly rewrite using `[h1]`. Rewrite using `[integral_complex_ofReal]`. Use `congr 1`.

Rewrite using `[integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg ‖F x‖) ((hF.cont.norm.pow 2).measurable.aestronglyMeasurable)]`. Use `congr 1`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`.
-/
theorem thetaO_norm_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → (∀ γ ∈ ratL T S, ∀ w, ‖F (γ + w)‖ = ‖F w‖) ∧ ∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ ≠ ⊤ ∧ ∫ x in 𝓕, F x * starRingEnd ℂ (F x) ∂μ = (((∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) := by
  intro D ψ hψ S T μ 𝓕 hC F hF
  haveI hB : BorelSpace (WO S T) := ⟨rfl⟩
  haveI hO : OpensMeasurableSpace (WO S T) := BorelSpace.opensMeasurable
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ w
    obtain ⟨ξ, rfl⟩ := hγ
    have hq := hF.quasi ξ w
    have e : ((incA D).toAddMonoidHom.mapMatrix ξ : WO S T) = ratW T S ξ := rfl
    rw [e, hq, norm_mul, hn, one_mul]
  · obtain ⟨M, hM⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hF
    have hle : ∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ ≤ ∫⁻ _x in 𝓕, ENNReal.ofReal M ^ 2 ∂μ := by
      refine lintegral_mono fun x => ?_
      gcongr
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM x)
    rw [setLIntegral_const, hC.2.2, mul_one] at hle
    exact ne_top_of_le_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hle
  · have h1 : ∀ x, F x * starRingEnd ℂ (F x) = (((‖F x‖ ^ 2 : ℝ)) : ℂ) := fun x => by
      rw [Complex.mul_conj']; push_cast; rfl
    simp_rw [h1]
    rw [integral_complex_ofReal]
    congr 1
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg ‖F x‖)
      ((hF.cont.norm.pow 2).measurable.aestronglyMeasurable)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

end GlobalTheory.ThetaSqInt
