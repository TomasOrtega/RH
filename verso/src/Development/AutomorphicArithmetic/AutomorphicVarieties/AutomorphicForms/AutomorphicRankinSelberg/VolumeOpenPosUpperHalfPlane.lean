import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory Set UpperHalfPlane in
/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem UpperTheory.V.Af.Rs.volume_open_pos_upper_half_plane (U : Set ℍ) (hU : IsOpen U) (hne : U.Nonempty) :
    0 < (volume : Measure ℍ) U := by
  rw [pos_iff_ne_zero]
  intro h0
  have hac : (volume.comap UpperHalfPlane.coe : Measure ℍ) ≪ (volume : Measure ℍ) := by
    rw [volume_def]
    refine withDensity_absolutelyContinuous' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine Measurable.aemeasurable (Measurable.coe_nnreal_ennreal ?_)
      refine Continuous.measurable ?_
      refine .pow (.div₀ continuous_const ?_ ?_) _
      · exact continuous_im.subtype_mk _
      · exact fun x ↦ NNReal.ne_iff.mp x.im_ne_zero
    · have hz : NNReal.mk z.im z.im_pos.le ≠ 0 := NNReal.ne_iff.mp z.im_ne_zero
      exact ENNReal.coe_ne_zero.mpr (pow_ne_zero _ (one_div_ne_zero hz))
  have h1 := hac h0
  rw [measurableEmbedding_coe.comap_apply] at h1
  exact ((isOpenEmbedding_coe.isOpenMap U hU).measure_pos volume (hne.image _)).ne' h1

open MeasureTheory Set UpperHalfPlane in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem UpperTheory.V.Af.Rs.fdPos :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.FdPos := by
  intro _ φ hc h0 hint z hz hpos
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall h0) hint]
  have hV : IsOpen {w : ℍ | 0 < φ w} := isOpen_lt continuous_const hc
  rw [ModularGroup.fd_eq_closure_fdo] at hz
  have hne : ({w : ℍ | 0 < φ w} ∩ ModularGroup.fdo).Nonempty :=
    mem_closure_iff.mp hz _ hV hpos
  refine (UpperTheory.V.Af.Rs.volume_open_pos_upper_half_plane _ (hV.inter ModularGroup.isOpen_fdo) hne).trans_le
    (measure_mono ?_)
  rintro w ⟨hw, hw'⟩
  exact ⟨ne_of_gt hw, ModularGroup.fdo_subset_fd hw'⟩
