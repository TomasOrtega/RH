import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IintEqEllStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHsNormSqDoubleCosetLeFatouStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.EllBound

/- English proof (translation)
Establish `hvv : ⟪v, v⟫_ℂ ≠ 0` using `inner_self_ne_zero.mpr hv`. Use `⟨(⟪v, v⟫_ℂ)⁻¹ • v, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[inner_smul_right]`. Conclude with `inv_mul_cancel₀ hvv`. Rewrite using `[inner_smul_left, map_inv₀, inner_conj_symm]`.

Conclude with `inv_mul_cancel₀ hvv`.
-/
theorem exists_inner_eq_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {v : E}
    (hv : v ≠ 0) : ∃ ξ : E, ⟪v, ξ⟫_ℂ = 1 ∧ ⟪ξ, v⟫_ℂ = 1 := by
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv
  refine ⟨(⟪v, v⟫_ℂ)⁻¹ • v, ?_, ?_⟩
  · rw [inner_smul_right]
    exact inv_mul_cancel₀ hvv
  · rw [inner_smul_left, map_inv₀, inner_conj_symm]
    exact inv_mul_cancel₀ hvv

/- English proof (translation)
Introduce `k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hS hS' ν hν l l' hl hl'`. Take `⟨w₀, hw₀, hlw₀⟩` from `hl.2.1`. Take `⟨w₀', hw₀', hlw₀'⟩` from `hl'.2.1`. Take `⟨ξ, hξ₁, hξ₂⟩` from `exists_inner_eq_one hlw₀`. Take `⟨ξ', hξ₁', hξ₂'⟩` from `exists_inner_eq_one hlw₀'`.

Establish `hbe : (⟪ξ, be (psiGen k r z c) π μS σ w₀ w₀ ξ⟫_ℂ).re = 1`. Rewrite using `[hl.2.2 w₀ hw₀ w₀ hw₀, rankOneInnerOperator_apply, inner_smul_right, hξ₁, hξ₂]`. Simplify using the standard rewrite rules. Establish `hbe' : (⟪ξ', be (psiGen k r z' c') π' μS' σ w₀' w₀' ξ'⟫_ℂ).re = 1`. Rewrite using `[hl'.2.2 w₀' hw₀' w₀' hw₀', rankOneInnerOperator_apply, inner_smul_right, hξ₁', hξ₂']`.

Simplify using the standard rewrite rules. Establish `hbound` using `GlobalTheory.T.lintegral_hsNormSq_doubleCoset_le_fatou k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' ν hν w₀' hw₀' w₀ hw₀ ξ ξ'`. Rewrite `hbound` using `[hbe, hbe', mul_one, mul_one]`. Use `le_trans (le_of_eq ?_) hbound` and prove the remaining obligations. Establish `hreg : ∀ᵐ γ ∂ν, Matrix.of γ ∈ Greg k r z z'` using `ae_iff.mpr hν.2.1`.

Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hreg] with γ hγ`. Rewrite using `[(GlobalTheory.T.iint_eq_ell_alt k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' l l' hl hl' _ hγ).2 w₀ hw₀ w₀' hw₀' ξ ξ', hξ₁, hξ₂']`. Simplify using the standard rewrite rules.
-/
theorem lintegral_hsNormSq_ell_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ ν : Measure (Mt k r), IsDis (Greg k r z z') μG μS μS' ν → ∀ (l : H → Wp) (l' : H → Wq), IsEll z (psiGen k r z c) π μS σ (DD σ w) l → IsEll z' (psiGen k r z' c') π' μS' σ (DD σ w) l' → ∫⁻ γ, ENNReal.ofReal (hsNormSq ((d : ℂ) • OO μG (fun x => l (σ x w)) (fun x => l' (σ x w)) (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal d⁻¹ := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hS hS' ν hν l l' hl hl'

  obtain ⟨w₀, hw₀, hlw₀⟩ := hl.2.1
  obtain ⟨w₀', hw₀', hlw₀'⟩ := hl'.2.1
  obtain ⟨ξ, hξ₁, hξ₂⟩ := exists_inner_eq_one hlw₀
  obtain ⟨ξ', hξ₁', hξ₂'⟩ := exists_inner_eq_one hlw₀'

  have hbe : (⟪ξ, be (psiGen k r z c) π μS σ w₀ w₀ ξ⟫_ℂ).re = 1 := by
    rw [hl.2.2 w₀ hw₀ w₀ hw₀, rankOneInnerOperator_apply, inner_smul_right, hξ₁, hξ₂]
    simp
  have hbe' : (⟪ξ', be (psiGen k r z' c') π' μS' σ w₀' w₀' ξ'⟫_ℂ).re = 1 := by
    rw [hl'.2.2 w₀' hw₀' w₀' hw₀', rankOneInnerOperator_apply, inner_smul_right, hξ₁', hξ₂']
    simp
  have hbound := GlobalTheory.T.lintegral_hsNormSq_doubleCoset_le_fatou k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' ν hν
    w₀' hw₀' w₀ hw₀ ξ ξ'
  rw [hbe, hbe', mul_one, mul_one] at hbound
  refine le_trans (le_of_eq ?_) hbound

  have hreg : ∀ᵐ γ ∂ν, Matrix.of γ ∈ Greg k r z z' := ae_iff.mpr hν.2.1
  refine lintegral_congr_ae ?_
  filter_upwards [hreg] with γ hγ
  rw [(GlobalTheory.T.iint_eq_ell_alt k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' l l' hl hl' _ hγ).2
    w₀ hw₀ w₀' hw₀' ξ ξ', hξ₁, hξ₂']
  simp

end GlobalTheory.SgInf.EllBound
