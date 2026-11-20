import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
import GroundTheory.AutomorphicForms.LocallyConstantCompact

noncomputable section

open MeasureTheory

namespace UpperTheory.Gal.LocD

/- English proof (translation)
Introduce `G _ _ _ _ _ _ B hB _ _ μ _ χ K hKo hKc hBK φ hφ`. Take `⟨hφB, K0, hK0o, hφK0⟩` from `mem_indF.1 hφ`. Use `set S : Set B := {b | (b : G) ∈ K} with hS`. Establish `hSo : IsOpen S` using `hKo.preimage continuous_subtype_val`. Establish `hSc : IsCompact S` using `(hB.isClosedEmbedding_subtypeVal).isCompact_preimage hKc`.

Establish `hSpos : 0 < μ S` using `hSo.measure_pos μ ⟨1, K.one_mem⟩`. Establish `hSfin : μ S < ⊤` using `hSc.measure_lt_top`. Establish `hr : (μ S).toReal ≠ 0` using `(ENNReal.toReal_pos hSpos.ne' hSfin.ne).ne'`. Establish `hr' : ((μ S).toReal : ℂ) ≠ 0` using `by exact_mod_cast hr`. Use `set c : ℂ := ((μ S).toReal : ℂ)⁻¹ with hc`.

Use `⟨fun g => if g ∈ K then c * φ g else 0, ?_, ?_⟩` and prove the remaining obligations. Set `K' : OpenSubgroup G` to `⟨K ⊓ K0, hKo.inter hK0o⟩`. Apply `GroundTheory.Automorphic.mem_locallyConstantCompactSupport_of_forall_mul_right (R := ℂ) K'` to reduce the goal to its premises. Conclude with `HasCompactSupport.intro hKc (fun g hg => if_neg hg)`. Introduce `g k hk`.

Establish `hk' : k ∈ K ∧ k ∈ K0` using `Subgroup.mem_inf.1 hk`. Simplify using `only [K.mul_mem_cancel_right hk'.1, hφK0 k hk'.2 g]`. Use function extensionality and compare the values at `g`. Take `⟨b0, hb0, k0, hk0, rfl⟩` from `hBK g`. Use `set b0' : B := ⟨b0, hb0⟩`.

Establish `key : ∀ b : B, ((b : G)⁻¹ * (b0 * k0) ∈ K) ↔ b ∈ (fun x => b0'⁻¹ * x) ⁻¹' S`. Introduce `b`. Simplify using `only [Set.mem_preimage, hS, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv, b0']`. Rewrite using `[← mul_assoc, K.mul_mem_cancel_right hk0, ← K.inv_mem_iff]`. Simplify using `[mul_inv_rev]`.

Establish `hTm : MeasurableSet ((fun x : B => b0'⁻¹ * x) ⁻¹' S)` using `(hSo.preimage (continuous_const.mul continuous_id)).measurableSet`. Establish `hint : (fun b : B => (χ b : ℂ) * (if ((b:G)⁻¹ * (b0 * k0)) ∈ K then c * φ ((b:G)⁻¹ * (b0*k0)) else 0)) = ((fun x : B => b0'⁻¹ * x) ⁻¹' S).indicator (fun _ => c * φ (b0 * k0))`. Use function extensionality and compare the values at `b`. Distinguish the cases in `h : ((b:G)⁻¹ * (b0 * k0)) ∈ K`. Rewrite using `[if_pos h, Set.indicator_of_mem ((key b).1 h)]`.

Establish `h1` using `hφB b⁻¹ (b0 * k0)`. Rewrite `h1` using `[Subgroup.coe_inv]`. Rewrite using `[h1]`. Establish `hu : (χ b : ℂ) * (χ b⁻¹ : ℂ) = 1`. Rewrite using `[← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]`.

Take the linear combination `(c * φ (b0 * k0)) * hu`. Rewrite using `[if_neg h, Set.indicator_of_notMem (fun h' => h ((key b).2 h')), mul_zero]`. Simplify using `only [pr]`. Rewrite using `[hint, integral_indicator_const _ hTm, measureReal_def, measure_preimage_mul]`. Rewrite using `[hc, Complex.real_smul]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem prSurj : PrSurj := by
  classical
  intro G _ _ _ _ _ _ B hB _ _ μ _ χ K hKo hKc hBK φ hφ
  obtain ⟨hφB, K0, hK0o, hφK0⟩ := mem_indF.1 hφ
  set S : Set B := {b | (b : G) ∈ K} with hS
  have hSo : IsOpen S := hKo.preimage continuous_subtype_val
  have hSc : IsCompact S := (hB.isClosedEmbedding_subtypeVal).isCompact_preimage hKc
  have hSpos : 0 < μ S := hSo.measure_pos μ ⟨1, K.one_mem⟩
  have hSfin : μ S < ⊤ := hSc.measure_lt_top
  have hr : (μ S).toReal ≠ 0 := (ENNReal.toReal_pos hSpos.ne' hSfin.ne).ne'
  have hr' : ((μ S).toReal : ℂ) ≠ 0 := by exact_mod_cast hr
  set c : ℂ := ((μ S).toReal : ℂ)⁻¹ with hc
  refine ⟨fun g => if g ∈ K then c * φ g else 0, ?_, ?_⟩
  · let K' : OpenSubgroup G := ⟨K ⊓ K0, hKo.inter hK0o⟩
    apply GroundTheory.Automorphic.mem_locallyConstantCompactSupport_of_forall_mul_right (R := ℂ) K'
    · exact HasCompactSupport.intro hKc (fun g hg => if_neg hg)
    · intro g k hk
      have hk' : k ∈ K ∧ k ∈ K0 := Subgroup.mem_inf.1 hk
      simp only [K.mul_mem_cancel_right hk'.1, hφK0 k hk'.2 g]
  · funext g
    obtain ⟨b0, hb0, k0, hk0, rfl⟩ := hBK g
    set b0' : B := ⟨b0, hb0⟩
    have key : ∀ b : B, ((b : G)⁻¹ * (b0 * k0) ∈ K) ↔ b ∈ (fun x => b0'⁻¹ * x) ⁻¹' S := by
      intro b
      simp only [Set.mem_preimage, hS, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv, b0']
      rw [← mul_assoc, K.mul_mem_cancel_right hk0, ← K.inv_mem_iff]
      simp [mul_inv_rev]
    have hTm : MeasurableSet ((fun x : B => b0'⁻¹ * x) ⁻¹' S) :=
      (hSo.preimage (continuous_const.mul continuous_id)).measurableSet
    have hint : (fun b : B => (χ b : ℂ) * (if ((b:G)⁻¹ * (b0 * k0)) ∈ K then c * φ ((b:G)⁻¹ * (b0*k0)) else 0))
        = ((fun x : B => b0'⁻¹ * x) ⁻¹' S).indicator (fun _ => c * φ (b0 * k0)) := by
      funext b
      by_cases h : ((b:G)⁻¹ * (b0 * k0)) ∈ K
      · rw [if_pos h, Set.indicator_of_mem ((key b).1 h)]
        have h1 := hφB b⁻¹ (b0 * k0)
        rw [Subgroup.coe_inv] at h1
        rw [h1]
        have hu : (χ b : ℂ) * (χ b⁻¹ : ℂ) = 1 := by
          rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
        linear_combination (c * φ (b0 * k0)) * hu
      · rw [if_neg h, Set.indicator_of_notMem (fun h' => h ((key b).2 h')), mul_zero]
    simp only [pr]
    rw [hint, integral_indicator_const _ hTm, measureReal_def, measure_preimage_mul]
    rw [hc, Complex.real_smul]
    field_simp

end UpperTheory.Gal.LocD

end
