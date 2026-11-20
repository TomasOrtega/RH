import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.KdMeasImageProd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntMuCD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.ContinuousMatrixExpCompact

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem eigenvalues_zero (ε : Fin n → Bool) : pev (0 : PCoord ε → ℂ) = 0 := by
  have h0 : pmat (0 : PCoord ε → ℂ) = 0 := by
    ext a b
    simp only [pmat]
    split_ifs <;> simp
  exact (pmat_isHermitian (0 : PCoord ε → ℂ)).eigenvalues_eq_zero_iff.2 h0

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem jacobian_zero (ε : Fin n → Bool) : Jac (0 : PCoord ε → ℂ) = 1 := by
  unfold Jac
  rw [eigenvalues_zero]
  simp [shc]

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem unitary_volume_pos (M : ℕ) : 0 < volU M := by
  unfold volU
  exact Finset.prod_pos fun i _ => by positivity

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem jacobian_near_one_of_small (ε : Fin n → Bool) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ C : Set (PCoord ε → ℂ), MeasurableSet C → (∀ z ∈ C, ‖z‖ < δ) →
      (∫⁻ z in C, ENNReal.ofReal (Jac z)) ≤ ENNReal.ofReal (1 + η) * volume C ∧
        ENNReal.ofReal (1 - η) * volume C ≤ ∫⁻ z in C, ENNReal.ofReal (Jac z) := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 (jac_continuous ε) 0 η hη
  have hpt : ∀ z : PCoord ε → ℂ, ‖z‖ < δ → |Jac z - 1| < η := fun z hz => by
    have := h z (by simpa [dist_zero_right] using hz)
    rwa [jacobian_zero, Real.dist_eq] at this
  refine ⟨δ, hδ, fun C hC hCδ => ⟨?_, ?_⟩⟩
  · rw [← setLIntegral_const]
    refine lintegral_mono_ae ((ae_restrict_iff' hC).2 (Filter.Eventually.of_forall fun z hz => ?_))
    have := abs_lt.1 (hpt z (hCδ z hz))
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [← setLIntegral_const]
    refine lintegral_mono_ae ((ae_restrict_iff' hC).2 (Filter.Eventually.of_forall fun z hz => ?_))
    have := abs_lt.1 (hpt z (hCδ z hz))
    exact ENNReal.ofReal_le_ofReal (by linarith)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Use the polynomial consequences of the given equalities and inequalities.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Use the polynomial consequences of the given equalities and inequalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem muPolar_near_one (ε : Fin n → Bool) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ (B : Set (KCo ε)) (C : Set (PCoord ε → ℂ)), MeasurableSet B → MeasurableSet C →
      (∀ w ∈ B, ‖w‖ < δ) → (∀ z ∈ C, ‖z‖ < δ) →
      muPolar ε (polSet (B ×ˢ C)) ≤
          ENNReal.ofReal ((1 + η) / (volU (pOf ε) * volU (qOf ε))) * (volume B * volume C) ∧
        ENNReal.ofReal ((1 - η) / (volU (pOf ε) * volU (qOf ε))) * (volume B * volume C) ≤
          muPolar ε (polSet (B ×ˢ C)) := by
  have hm0 : 0 < min η 1 := lt_min hη one_pos
  set t : ℝ := min η 1 / 3 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 / 3 := by
    have := min_le_right η 1
    rw [ht]; linarith
  have ht2 : 3 * t ≤ η := by
    have := min_le_left η 1
    rw [ht]; linarith
  obtain ⟨δ1, hδ1, hdk⟩ := dk_density ε t ht0
  obtain ⟨δ2, hδ2, hJ⟩ := jacobian_near_one_of_small ε t ht0
  obtain ⟨δ3, hδ3, hinj⟩ := exp_compact_injOn ε
  refine ⟨min δ1 (min δ2 δ3), lt_min hδ1 (lt_min hδ2 hδ3), fun B C hB hC hBδ hCδ => ?_⟩
  have hB1 : ∀ w ∈ B, ‖w‖ < δ1 := fun w hw => lt_of_lt_of_le (hBδ w hw) (min_le_left _ _)
  have hB3 : ∀ w ∈ B, ‖w‖ < δ3 := fun w hw =>
    lt_of_lt_of_le (hBδ w hw) ((min_le_right _ _).trans (min_le_right _ _))
  have hC2 : ∀ z ∈ C, ‖z‖ < δ2 := fun z hz =>
    lt_of_lt_of_le (hCδ z hz) ((min_le_right _ _).trans (min_le_left _ _))
  have hA := measurableSet_exp_image hB (hinj.mono fun w hw => hB3 w hw)
  rw [polar_measure_product_eq hA hC]
  obtain ⟨hd1, hd2⟩ := hdk B hB hB1
  obtain ⟨hj1, hj2⟩ := hJ C hC hC2
  have hV : 0 < volU (pOf ε) * volU (qOf ε) := mul_pos (unitary_volume_pos _) (unitary_volume_pos _)
  set V := volU (pOf ε) * volU (qOf ε) with hVdef
  have hA' : expImageOfCompact B = {k | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)} := rfl
  rw [hA']
  constructor
  · calc (∫⁻ z in C, ENNReal.ofReal (Jac z)) * dk ε {k | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)}
        ≤ (ENNReal.ofReal (1 + t) * volume C) * (ENNReal.ofReal ((1 + t) / V) * volume B) :=
          mul_le_mul' hj1 hd1
      _ = ENNReal.ofReal ((1 + t) * ((1 + t) / V)) * (volume B * volume C) := by
          rw [ENNReal.ofReal_mul (by linarith)]; ring
      _ ≤ ENNReal.ofReal ((1 + η) / V) * (volume B * volume C) := by
          gcongr
          rw [← mul_div_assoc]
          apply div_le_div_of_nonneg_right _ hV.le
          nlinarith
  · calc ENNReal.ofReal ((1 - η) / V) * (volume B * volume C)
        ≤ ENNReal.ofReal ((1 - t) * ((1 - t) / V)) * (volume B * volume C) := by
          gcongr
          rw [← mul_div_assoc]
          apply div_le_div_of_nonneg_right _ hV.le
          nlinarith
      _ = (ENNReal.ofReal (1 - t) * volume C) * (ENNReal.ofReal ((1 - t) / V) * volume B) := by
          rw [ENNReal.ofReal_mul (by linarith)]; ring
      _ ≤ (∫⁻ z in C, ENNReal.ofReal (Jac z)) * dk ε {k | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)} :=
          mul_le_mul' hj2 hd2

end ReciprocityTheory.ChartRestriction.DS
