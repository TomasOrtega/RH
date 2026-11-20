import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DiffBound
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.TorusReduction

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

def ccTranslate (g : normOneGL K n) (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    CompactlySupportedContinuousMap (normOneGL K n) ℂ :=
  ⟨⟨fun w => f (g⁻¹ * w), f.continuous.comp (continuous_const_mul _)⟩,
    f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft g⁻¹)⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem rconv_mul_eq (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (x g : normOneGL K n) :
    rconv Γ₁ μ f φ (x * g) = rconv Γ₁ μ (ccTranslate g f) φ x := by
  unfold rconv
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  change f ((x * g)⁻¹ * z) * _ = f (g⁻¹ * (x⁻¹ * z)) * _
  rw [mul_inv_rev, mul_assoc]

/- English proof (translation)
Rewrite the conclusion repeatedly using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_altSign_rconv_eq (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (x : normOneGL K n) {k : ℕ}
    (C : (Fin k → Bool) → ArchUnits K n) :
    ∑ ε, (altSign ε : ℂ) * rconv Γ₁ μ f φ (x * archProj K n (C ε)) =
      rconv Γ₁ μ (fun w => ∑ ε, (altSign ε : ℂ) * f ((archProj K n (C ε))⁻¹ * w)) φ x := by
  simp_rw [rconv_mul_eq μ f φ x]
  unfold rconv
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun ε _ => (integrable_rconv Γ₁ μ _ φ x).const_mul _]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun ε _ => ?_
  simp only [ccTranslate]
  change _ * (f ((archProj K n (C ε))⁻¹ * (x⁻¹ * z)) * _) = _
  ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem enorm_sum_altSign_rconv_sq_le (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (x : normOneGL K n) {k : ℕ} {𝒞 : Set (ArchUnits K n)}
    (h𝒞 : IsCompact 𝒞) (C : (Fin k → Bool) → ArchUnits K n) (hC : ∀ ε, C ε ∈ 𝒞) {b : ℝ}
    (hb : ∀ w, ‖∑ ε, (altSign ε : ℂ) * f ((archProj K n (C ε))⁻¹ * w)‖ ≤ b) {m : ℕ}
    (hm : ∀ z : normOneGL K n, {γ : Γ₁ | γ • z ∈ (fun y => x * y) ''
      (archProj K n '' 𝒞 * tsupport (f : normOneGL K n → ℂ))}.encard ≤ m) :
    ‖∑ ε, (altSign ε : ℂ) * rconv Γ₁ μ f φ (x * archProj K n (C ε))‖ₑ ^ 2 ≤
      ENNReal.ofReal b ^ 2 * μ (archProj K n '' 𝒞 * tsupport (f : normOneGL K n → ℂ)) *
        (m * ‖φ‖ₑ ^ 2) := by
  set Q := archProj K n '' 𝒞 * tsupport (f : normOneGL K n → ℂ)
  have hQ : IsCompact Q := (h𝒞.image continuous_archProj).mul f.hasCompactSupport
  have hsupp : ∀ w ∉ Q, ∑ ε, (altSign ε : ℂ) * f ((archProj K n (C ε))⁻¹ * w) = 0 := by
    intro w hw
    refine Finset.sum_eq_zero fun ε _ => ?_
    have : (archProj K n (C ε))⁻¹ * w ∉ tsupport (f : normOneGL K n → ℂ) := fun h' =>
      hw ⟨archProj K n (C ε), ⟨C ε, hC ε, rfl⟩, _, h', mul_inv_cancel_left _ _⟩
    rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
  set Ψ : CompactlySupportedContinuousMap (normOneGL K n) ℂ :=
    ⟨⟨fun w => ∑ ε, (altSign ε : ℂ) * f ((archProj K n (C ε))⁻¹ * w),
      continuous_finsetSum _ fun ε _ => continuous_const.mul
        (f.continuous.comp (continuous_const_mul _))⟩, HasCompactSupport.intro hQ hsupp⟩
  rw [sum_altSign_rconv_eq μ f φ x C]
  have hS : MeasurableSet ((fun y => x * y) '' Q) := (hQ.image (continuous_const_mul x)).measurableSet
  have h1 := enorm_rconv_sq_le Γ₁ μ Ψ φ x hS (fun y hy => hsupp _ fun hq => hy ⟨_, hq, by simp⟩) hm
  refine h1.trans ?_
  gcongr
  calc ∫⁻ y, ‖Ψ y‖ₑ ^ 2 ∂μ = ∫⁻ y in Q, ‖Ψ y‖ₑ ^ 2 ∂μ := by
        rw [← lintegral_indicator hQ.measurableSet]
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ Q
        · rw [indicator_of_mem hy]
        · rw [indicator_of_notMem hy]
          change ‖∑ ε, (altSign ε : ℂ) * f ((archProj K n (C ε))⁻¹ * y)‖ₑ ^ 2 = 0
          rw [hsupp y hy]
          simp
    _ ≤ ∫⁻ _ in Q, ENNReal.ofReal b ^ 2 ∂μ := by
        refine setLIntegral_mono' hQ.measurableSet fun y _ => ?_
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hb y)
    _ = ENNReal.ofReal b ^ 2 * μ Q := by rw [setLIntegral_const]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
