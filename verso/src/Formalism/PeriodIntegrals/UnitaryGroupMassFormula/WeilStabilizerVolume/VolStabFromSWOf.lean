import Mathlib
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.VolStabFromSWW

noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hE M J hJ ha hc hJ' a ha1 ha2 X0 hT hdet`. Use `⟨h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet, fun ψ hψ => ?_⟩` and prove the remaining obligations. Use `⟨ha.1, fun μ hμ => ?_⟩` and prove the remaining obligations. Use `⟨h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ, fun νX hν => ?_⟩` and prove the remaining obligations. Use `⟨h3 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν, fun μ' hμ' => ?_⟩` and prove the remaining obligations.

Take `⟨hμ'H, hμ'C⟩` from `hμ'`. Use `⟨(ha.2 μ hμ).1, fun 𝓕 h𝓕 => ?_⟩` and prove the remaining obligations. Use `⟨h4 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ' hμ'H, fun 𝓕' h𝓕' => ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ0, hadm, hI⟩` from `h7 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν μ' hμ'H hμ'C`. Establish `e1` using `h5 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν _ hadm`.

Unfold `meanC at e1`. Establish `hθ : ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h ∂μ ≠ 0`. Introduce `h0`. Rewrite `e1` using `[h0, smul_zero]`. Conclude with `hI e1.symm`.

Take `⟨hfin, e2⟩` from `h6 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν μ' hμ'H hμ'C 𝓕' h𝓕' φ hφ0 hadm hθ`. Rewrite `e1` using `[e2, smul_smul]`. Establish `hc1 : (μ 𝓕).toReal⁻¹ * (μ' 𝓕').toReal = 1`. Establish `e3 : ((((μ 𝓕).toReal⁻¹ * (μ' 𝓕').toReal : ℝ)) : ℂ) * ∫ X, (φ X : ℂ) ∂νX = 1 * ∫ X, (φ X : ℂ) ∂νX`. Rewrite using `[one_mul, ← Complex.real_smul]`.

Conclude with `e1`. Conclude with `mul_right_cancel₀ hI e3` after adjusting the coercions. Establish `h0 : (μ 𝓕).toReal ≠ 0`. Introduce `h0`. Rewrite `hc1` using `[h0, inv_zero, zero_mul]`.

Conclude with `zero_ne_one hc1`. Establish `e4 : (μ 𝓕).toReal = (μ' 𝓕').toReal` using `(inv_mul_eq_one₀ h0).1 hc1`. Conclude with `(ENNReal.toReal_eq_toReal_iff' hfin ((ha.2 μ hμ).2 𝓕 h𝓕).ne).1 e4.symm`.
-/
theorem volStabFromSW_of (h1 : ExChar) (h2 : ExOmT) (h3 : ExStab) (h4 : ExFDStab)
    (h5 : SWeqOm) (h6 : Unfold) (h7 : PosTest) : PI.VolStabW.VolStabFromSWW := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc hJ' a ha1 ha2 X0 hT hdet
  refine ⟨h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet, fun ψ hψ => ?_⟩
  refine ⟨ha.1, fun μ hμ => ?_⟩
  refine ⟨h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ, fun νX hν => ?_⟩
  refine ⟨h3 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν, fun μ' hμ' => ?_⟩
  obtain ⟨hμ'H, hμ'C⟩ := hμ'
  refine ⟨(ha.2 μ hμ).1, fun 𝓕 h𝓕 => ?_⟩
  refine ⟨h4 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ' hμ'H, fun 𝓕' h𝓕' => ?_⟩
  obtain ⟨φ, hφ0, hadm, hI⟩ := h7 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν μ' hμ'H hμ'C
  have e1 := h5 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν _ hadm
  unfold meanC at e1
  have hθ : ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ))
      {X | gramE σ J X = gramE σ J X0} h ∂μ ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at e1
    exact hI e1.symm
  obtain ⟨hfin, e2⟩ :=
    h6 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν μ' hμ'H hμ'C 𝓕' h𝓕'
      φ hφ0 hadm hθ
  rw [e2, smul_smul] at e1
  have hc1 : (μ 𝓕).toReal⁻¹ * (μ' 𝓕').toReal = 1 := by
    have e3 : ((((μ 𝓕).toReal⁻¹ * (μ' 𝓕').toReal : ℝ)) : ℂ) * ∫ X, (φ X : ℂ) ∂νX =
        1 * ∫ X, (φ X : ℂ) ∂νX := by
      rw [one_mul, ← Complex.real_smul]
      exact e1
    exact_mod_cast mul_right_cancel₀ hI e3
  have h0 : (μ 𝓕).toReal ≠ 0 := by
    intro h0
    rw [h0, inv_zero, zero_mul] at hc1
    exact zero_ne_one hc1
  have e4 : (μ 𝓕).toReal = (μ' 𝓕').toReal := (inv_mul_eq_one₀ h0).1 hc1
  exact (ENNReal.toReal_eq_toReal_iff' hfin ((ha.2 μ hμ).2 𝓕 h𝓕).ne).1 e4.symm

end PI.VolStabW
