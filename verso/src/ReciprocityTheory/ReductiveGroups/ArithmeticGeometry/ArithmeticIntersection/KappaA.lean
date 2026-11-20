import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt

open MeasureTheory Set
open scoped Pointwise

namespace ReciprocityTheory.ChartRestriction.G.AI

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem cone_preimage (L : E3 ≃ₗᵢ[ℝ] E3) (s : Set S2) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((fun n : S2 => (⟨L n, by simp⟩ : S2)) ⁻¹' s) : Set E3) =
      L ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E3)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul, Set.mem_image]
  constructor
  · rintro ⟨r, hr, _, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨r, hr, _, ⟨_, hn, rfl⟩, by simp⟩
  · rintro ⟨r, hr, _, ⟨m, hm, rfl⟩, hx⟩
    refine ⟨r, hr, _, ⟨⟨L.symm m, by simp⟩, ?_, rfl⟩, ?_⟩
    · convert hm using 1
      ext
      simp
    · apply L.injective
      rw [← hx]
      simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem measurable_sphereMap (L : E3 ≃ₗᵢ[ℝ] E3) :
    Measurable (fun n : S2 => (⟨L n, by simp⟩ : S2)) := ((L.continuous.comp continuous_subtype_val).subtype_mk _).measurable

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem toSphere_measurePreserving (L : E3 ≃ₗᵢ[ℝ] E3) :
    MeasurePreserving (fun n : S2 => (⟨L n, by simp⟩ : S2))
      (volume : Measure E3).toSphere (volume : Measure E3).toSphere := by
  refine ⟨measurable_sphereMap L, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_sphereMap L) hs, Measure.toSphere_apply' _ hs,
    Measure.toSphere_apply' _ (measurable_sphereMap L hs), cone_preimage]
  congr 1
  have hmp : MeasurePreserving (L.toHomeomorph.toMeasurableEquiv) (volume : Measure E3) volume :=
    L.measurePreserving
  exact hmp.measure_preimage_equiv _

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem sphereInv_thm : SphereInvStatement := by
  refine ⟨?_, fun L => ?_⟩
  · have h1 : (volume : Measure E3).toSphere Set.univ ≠ 0 := by
      rw [Measure.toSphere_apply_univ]
      refine mul_ne_zero (by simp) ?_
      exact (Metric.measure_ball_pos _ _ one_pos).ne'
    have h2 : (volume : Measure E3).toSphere Set.univ ≠ ⊤ := measure_ne_top _ _
    constructor
    rw [sphereMeasure, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h1 h2]
  · have hL := toSphere_measurePreserving L
    refine ⟨hL.measurable, ?_⟩
    rw [sphereMeasure, Measure.map_smul, hL.map_eq]

end ReciprocityTheory.ChartRestriction.G.AI
