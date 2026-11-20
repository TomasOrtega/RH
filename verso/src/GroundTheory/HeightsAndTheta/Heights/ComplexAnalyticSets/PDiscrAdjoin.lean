import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDiscrAdjoin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open Polynomial

/- English proof (translation)
Introduce `R K L _ _ _ _ _ _ _ _ _ _ _ _ ℓ hℓ hadj`. Establish `hK : IsIntegral K ℓ` using `Algebra.IsIntegral.isIntegral ℓ`. Establish `hFK : minpoly K ℓ = (minpoly R ℓ).map (algebraMap R K)` using `minpoly.isIntegrallyClosed_eq_field_fractions' K hℓ`. Establish `hFm : (minpoly R ℓ).Monic` using `minpoly.monic hℓ`. Establish `hinj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`.

Establish `hdegK : (minpoly K ℓ).natDegree = (minpoly R ℓ).natDegree`. Rewrite using `[hFK, natDegree_map_eq_of_injective hinj]`. Establish `hdeg : (minpoly R ℓ).natDegree = Module.finrank K L`. Establish `h1` using `IntermediateField.adjoin.finrank hK`. Rewrite `h1` using `[hadj, IntermediateField.finrank_top', hdegK]`.

Conclude with `h1.symm`. Establish `hpos : 0 < (minpoly R ℓ).natDegree` using `minpoly.natDegree_pos hℓ`. Establish `hF'deg : (derivative (minpoly R ℓ)).natDegree ≤ (minpoly R ℓ).natDegree - 1` using `natDegree_derivative_le _`. Establish `hres` using `resultant_deriv (f := minpoly R ℓ) (natDegree_pos_iff_degree_pos.mp hpos)`. Rewrite `hres` using `[hFm.leadingCoeff, mul_one]`.

Establish `hdisc : (minpoly R ℓ).discr = (-1) ^ ((minpoly R ℓ).natDegree * ((minpoly R ℓ).natDegree - 1) / 2) * resultant (minpoly R ℓ) (derivative (minpoly R ℓ)) (minpoly R ℓ).natDegree ((minpoly R ℓ).natDegree - 1)`. Rewrite using `[hres, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]`. Use `⟨hdeg, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `hR : resultant (minpoly R ℓ) (derivative (minpoly R ℓ)) (minpoly R ℓ).natDegree ((minpoly R ℓ).natDegree - 1) = 0` using `by rw [hres, h0, mul_zero]`.

Establish `hRK` using `congrArg (algebraMap R K) hR`. Rewrite `hRK` using `[← resultant_map_map, map_zero, ← derivative_map, ← hFK, ← hdegK]`. Establish `hsep : (minpoly K ℓ).Separable` using `Algebra.IsSeparable.isSeparable K ℓ`. Establish `hle : (derivative (minpoly K ℓ)).natDegree ≤ (minpoly K ℓ).natDegree - 1` using `natDegree_derivative_le _`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le hle`.

Rewrite `hRK` using `[hk, resultant_add_right_deg _ _ _ _ k le_rfl, coeff_natDegree, (minpoly.monic hK).leadingCoeff, one_pow, one_mul]`. Conclude with `resultant_ne_zero _ _ hsep hRK`. Introduce `z hz`. Take `⟨p, q, -, -, hpq⟩` from `exists_mul_add_mul_eq_C_resultant (minpoly R ℓ) (derivative (minpoly R ℓ)) le_rfl hF'deg (Or.inl hpos.ne')`. Establish `hev` using `congrArg (aeval ℓ) hpq`.

Simplify using `only [map_add, map_mul, minpoly.aeval, zero_mul, zero_add, aeval_C] at hev`. Establish `hadjK : Algebra.adjoin K {ℓ} = ⊤`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hK.isAlgebraic, hadj, IntermediateField.top_toSubalgebra]`. Establish `hzmem : z ∈ (Algebra.traceForm K L).dualSubmodule (Subalgebra.toSubmodule (Algebra.adjoin R {ℓ}))`. Rewrite using `[LinearMap.BilinForm.mem_dualSubmodule]`.

Introduce `y hy`. Rewrite using `[Submodule.mem_one]`. Establish `hyint : IsIntegral R y` using `adjoin_le_integralClosure hℓ hy`. Establish `htr : IsIntegral R (Algebra.trace K L (z * y))` using `Algebra.isIntegral_trace (hz.mul hyint)`. Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.mp htr`.

Conclude with `⟨r, by simpa [Algebra.traceForm_apply] using hr⟩`. Rewrite `hzmem` using `[traceForm_dualSubmodule_adjoin R K hadjK hℓ]`. Take `⟨w, hw, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hzmem`. Establish `hd : aeval ℓ (derivative (minpoly K ℓ)) = aeval ℓ (derivative (minpoly R ℓ))`. Rewrite using `[hFK, derivative_map, aeval_map_algebraMap]`.

Rewrite using `[hd]`. Establish `hq : aeval ℓ q ∈ Algebra.adjoin R {ℓ}` using `aeval_mem_adjoin_singleton R ℓ`. Establish `hw' : w ∈ Algebra.adjoin R {ℓ}` using `hw`. Establish `key : (minpoly R ℓ).discr • ((aeval ℓ (derivative (minpoly R ℓ)))⁻¹ • w) = ((-1 : L) ^ ((minpoly R ℓ).natDegree * ((minpoly R ℓ).natDegree - 1) / 2) * aeval ℓ q * w) * (aeval ℓ (derivative (minpoly R ℓ)) * (aeval ℓ (derivative (minpoly R ℓ)))⁻¹)`. Rewrite using `[hdisc, Algebra.smul_def, smul_eq_mul, map_mul, ← hev, map_pow, map_neg, map_one]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Distinguish the cases in `hd0 : aeval ℓ (derivative (minpoly R ℓ)) = 0`. Rewrite using `[hd0, zero_mul, mul_zero]`. Conclude with `zero_mem _`.

Rewrite using `[mul_inv_cancel₀ hd0, mul_one]`. Conclude with `mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) hq) hw'`.
-/
theorem DiscrAdjoin.proof : DiscrAdjoin.Statement := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ _ ℓ hℓ hadj
  have hK : IsIntegral K ℓ := Algebra.IsIntegral.isIntegral ℓ
  have hFK : minpoly K ℓ = (minpoly R ℓ).map (algebraMap R K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hℓ
  have hFm : (minpoly R ℓ).Monic := minpoly.monic hℓ
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hdegK : (minpoly K ℓ).natDegree = (minpoly R ℓ).natDegree := by
    rw [hFK, natDegree_map_eq_of_injective hinj]
  have hdeg : (minpoly R ℓ).natDegree = Module.finrank K L := by
    have h1 := IntermediateField.adjoin.finrank hK
    rw [hadj, IntermediateField.finrank_top', hdegK] at h1
    exact h1.symm
  have hpos : 0 < (minpoly R ℓ).natDegree := minpoly.natDegree_pos hℓ
  have hF'deg : (derivative (minpoly R ℓ)).natDegree ≤ (minpoly R ℓ).natDegree - 1 :=
    natDegree_derivative_le _
  have hres := resultant_deriv (f := minpoly R ℓ) (natDegree_pos_iff_degree_pos.mp hpos)
  rw [hFm.leadingCoeff, mul_one] at hres
  have hdisc : (minpoly R ℓ).discr = (-1) ^ ((minpoly R ℓ).natDegree *
      ((minpoly R ℓ).natDegree - 1) / 2) * resultant (minpoly R ℓ) (derivative (minpoly R ℓ))
        (minpoly R ℓ).natDegree ((minpoly R ℓ).natDegree - 1) := by
    rw [hres, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  refine ⟨hdeg, ?_, ?_⟩
  · intro h0
    have hR : resultant (minpoly R ℓ) (derivative (minpoly R ℓ)) (minpoly R ℓ).natDegree
        ((minpoly R ℓ).natDegree - 1) = 0 := by rw [hres, h0, mul_zero]
    have hRK := congrArg (algebraMap R K) hR
    rw [← resultant_map_map, map_zero, ← derivative_map, ← hFK, ← hdegK] at hRK
    have hsep : (minpoly K ℓ).Separable := Algebra.IsSeparable.isSeparable K ℓ
    have hle : (derivative (minpoly K ℓ)).natDegree ≤ (minpoly K ℓ).natDegree - 1 :=
      natDegree_derivative_le _
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, resultant_add_right_deg _ _ _ _ k le_rfl, coeff_natDegree, (minpoly.monic hK).leadingCoeff,
      one_pow, one_mul] at hRK
    exact resultant_ne_zero _ _ hsep hRK
  · intro z hz
    obtain ⟨p, q, -, -, hpq⟩ := exists_mul_add_mul_eq_C_resultant (minpoly R ℓ)
      (derivative (minpoly R ℓ)) le_rfl hF'deg (Or.inl hpos.ne')
    have hev := congrArg (aeval ℓ) hpq
    simp only [map_add, map_mul, minpoly.aeval, zero_mul, zero_add, aeval_C] at hev
    have hadjK : Algebra.adjoin K {ℓ} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hK.isAlgebraic, hadj,
        IntermediateField.top_toSubalgebra]
    have hzmem : z ∈ (Algebra.traceForm K L).dualSubmodule
        (Subalgebra.toSubmodule (Algebra.adjoin R {ℓ})) := by
      rw [LinearMap.BilinForm.mem_dualSubmodule]
      intro y hy
      rw [Submodule.mem_one]
      have hyint : IsIntegral R y := adjoin_le_integralClosure hℓ hy
      have htr : IsIntegral R (Algebra.trace K L (z * y)) := Algebra.isIntegral_trace (hz.mul hyint)
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp htr
      exact ⟨r, by simpa [Algebra.traceForm_apply] using hr⟩
    rw [traceForm_dualSubmodule_adjoin R K hadjK hℓ] at hzmem
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hzmem
    have hd : aeval ℓ (derivative (minpoly K ℓ)) = aeval ℓ (derivative (minpoly R ℓ)) := by
      rw [hFK, derivative_map, aeval_map_algebraMap]
    rw [hd]
    have hq : aeval ℓ q ∈ Algebra.adjoin R {ℓ} := aeval_mem_adjoin_singleton R ℓ
    have hw' : w ∈ Algebra.adjoin R {ℓ} := hw
    have key : (minpoly R ℓ).discr • ((aeval ℓ (derivative (minpoly R ℓ)))⁻¹ • w) =
        ((-1 : L) ^ ((minpoly R ℓ).natDegree * ((minpoly R ℓ).natDegree - 1) / 2) * aeval ℓ q * w) *
          (aeval ℓ (derivative (minpoly R ℓ)) * (aeval ℓ (derivative (minpoly R ℓ)))⁻¹) := by
      rw [hdisc, Algebra.smul_def, smul_eq_mul, map_mul, ← hev, map_pow, map_neg, map_one]
      ring
    rw [key]
    by_cases hd0 : aeval ℓ (derivative (minpoly R ℓ)) = 0
    · rw [hd0, zero_mul, mul_zero]
      exact zero_mem _
    · rw [mul_inv_cancel₀ hd0, mul_one]
      exact mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) hq) hw'

end GroundTheory.Heights₂.Heights.ComplexSets
