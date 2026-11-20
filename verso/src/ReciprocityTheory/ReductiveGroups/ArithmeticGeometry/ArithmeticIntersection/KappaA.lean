import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt

open MeasureTheory Set
open scoped Pointwise

namespace ReciprocityTheory.ChartRestriction.G.AI

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_smul, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, _, ⟨n, hn, rfl⟩, rfl⟩`. Conclude with `⟨r, hr, _, ⟨_, hn, rfl⟩, by simp⟩`.

Introduce and unpack `⟨r, hr, _, ⟨m, hm, rfl⟩, hx⟩`. Use `⟨r, hr, _, ⟨⟨L.symm m, by simp⟩, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Use `hm using 1` and compare the differences between its conclusion and the goal. Use `ext`. Simplify using the standard rewrite rules.

Apply `L.injective` to reduce the goal to its premises. Rewrite using `[← hx]`. Simplify using the standard rewrite rules.
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
The claim follows from `((L.continuous.comp continuous_subtype_val).subtype_mk _).measurable`.
-/
theorem measurable_sphereMap (L : E3 ≃ₗᵢ[ℝ] E3) :
    Measurable (fun n : S2 => (⟨L n, by simp⟩ : S2)) := ((L.continuous.comp continuous_subtype_val).subtype_mk _).measurable

/- English proof (translation)
Use `⟨measurable_sphereMap L, ?_⟩` and prove the remaining obligations. Use extensionality with `s hs`. Rewrite using `[Measure.map_apply (measurable_sphereMap L) hs, Measure.toSphere_apply' _ hs, Measure.toSphere_apply' _ (measurable_sphereMap L hs), cone_preimage]`. Use `congr 1`. Establish `hmp : MeasurePreserving (L.toHomeomorph.toMeasurableEquiv) (volume : Measure E3) volume` using `L.measurePreserving`.

Conclude with `hmp.measure_preimage_equiv _`.
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
Use `⟨?_, fun L => ?_⟩` and prove the remaining obligations. Establish `h1 : (volume : Measure E3).toSphere Set.univ ≠ 0`. Rewrite using `[Measure.toSphere_apply_univ]`. Use `mul_ne_zero (by simp) ?_` and prove the remaining obligations. Conclude with `(Metric.measure_ball_pos _ _ one_pos).ne'`.

Establish `h2 : (volume : Measure E3).toSphere Set.univ ≠ ⊤` using `measure_ne_top _ _`. Prove the components needed by the constructor for the conclusion. Rewrite using `[sphereMeasure, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h1 h2]`. Establish `hL` using `toSphere_measurePreserving L`. Use `⟨hL.measurable, ?_⟩` and prove the remaining obligations.

Rewrite using `[sphereMeasure, Measure.map_smul, hL.map_eq]`.
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
