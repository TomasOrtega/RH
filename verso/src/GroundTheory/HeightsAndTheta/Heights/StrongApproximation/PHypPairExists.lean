import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix ReciprocityTheory.ChartRestriction.G.SA

/- English proof (translation)
Introduce `E _ σ hσ h2 N J hJ hdet e he0 hee`. Establish `hw : ∃ j, ∑ i, e i * J i j ≠ 0`. Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, not_not] at h`. Establish `h0 : e ᵥ* J = 0`.

Use extensionality with `j`. Simplify `h j` using `[vecMul, dotProduct]`. Apply `he0` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Take `⟨j, hj⟩` from `hw`.

Establish `hsingle : hf σ J e (Pi.single j 1) = ∑ i, e i * J i j`. Simplify using `only [hf]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules.

Introduce `k _ hk`. Simplify using `[hk]`. Simplify using the standard rewrite rules. Take `⟨a, hea⟩ : ∃ a : Fin N → E, hf σ J e a = 1` from `⟨σ (∑ i, e i * J i j)⁻¹ • Pi.single j 1, by`. Rewrite using `[hf_smul_right, hsingle, hσ, inv_mul_cancel₀ hj]⟩`.

Establish `hae : hf σ J a e = 1`. Rewrite using `[← hf_symm hσ hJ, hea, map_one]`. Establish `haa : σ (hf σ J a a) = hf σ J a a` using `hf_symm hσ hJ a a`. Use `set t : E := -(hf σ J a a) / 2 with ht_def`. Establish `hσ2 : σ 2 = 2` using `map_ofNat σ 2`.

Establish `ht : t + σ t = -(hf σ J a a)`. Rewrite using `[ht_def, map_div₀, map_neg, haa, hσ2]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨a + t • e, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_left, hf_smul_right, hf_smul_right, hea, hae, hee]`. Take the linear combination `ht`. Rewrite using `[hf_add_right, hf_smul_right, hea, hee, mul_zero, add_zero]`.
-/
theorem HypPairExists.proof : HypPairExists.Statement := by
  intro E _ σ hσ h2 N J hJ hdet e he0 hee

  have hw : ∃ j, ∑ i, e i * J i j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have h0 : e ᵥ* J = 0 := by
      ext j
      simpa [vecMul, dotProduct] using h j
    apply he0
    calc e = e ᵥ* (J * J⁻¹) := by rw [mul_nonsing_inv J hdet, vecMul_one]
      _ = (e ᵥ* J) ᵥ* J⁻¹ := by rw [vecMul_vecMul]
      _ = 0 := by rw [h0, zero_vecMul]
  obtain ⟨j, hj⟩ := hw
  have hsingle : hf σ J e (Pi.single j 1) = ∑ i, e i * J i j := by
    simp only [hf]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [hk]
    · simp

  obtain ⟨a, hea⟩ : ∃ a : Fin N → E, hf σ J e a = 1 :=
    ⟨σ (∑ i, e i * J i j)⁻¹ • Pi.single j 1, by
      rw [hf_smul_right, hsingle, hσ, inv_mul_cancel₀ hj]⟩
  have hae : hf σ J a e = 1 := by
    rw [← hf_symm hσ hJ, hea, map_one]
  have haa : σ (hf σ J a a) = hf σ J a a := hf_symm hσ hJ a a
  set t : E := -(hf σ J a a) / 2 with ht_def
  have hσ2 : σ 2 = 2 := map_ofNat σ 2
  have ht : t + σ t = -(hf σ J a a) := by
    rw [ht_def, map_div₀, map_neg, haa, hσ2]
    field_simp
    ring
  refine ⟨a + t • e, ?_, ?_⟩
  · rw [hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_left, hf_smul_right,
      hf_smul_right, hea, hae, hee]
    linear_combination ht
  · rw [hf_add_right, hf_smul_right, hea, hee, mul_zero, add_zero]

end StrongApprox

end GroundTheory.Heights₂.Heights
